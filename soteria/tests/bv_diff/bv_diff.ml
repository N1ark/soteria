(** Differential harness: old simplifier vs new simplifier.

    {v
    bv_diff [N [SEED]] [--mode strict|comm|exhaustive] [--allow-order-only]
            [--mutate NAME] [--self-test] [--report K] [--batch K] [--coverage] [--new real|standin]
    v}

    Replays [N] random well-typed terms (or, in [exhaustive] mode, every shallow
    term of the small pool) through the public smart constructors of both sides,
    in the same call order, and compares the results with {!Iso}. See the module
    comments of [Tm], [Side], [Iso], [Gen], [Exhaustive] and [Cov]. *)

open Tm

module Old =
  Old_side.Api
    (Old_side.A_typed)
    (struct
      let name = "old"
    end)

module type NEW = sig
  include Side.SIDE

  val available : bool
  val label : string
end

module Run (New : NEW) = struct
  let old_log : Cov.key list ref = ref []
  let new_log : Cov.key list ref = ref []

  (* Every node built through the front API is kept alive (until [batch_end], by
     default the whole run): the hash-cons tables are weak, dead terms are
     collected by each table independently, and a term that is recreated later
     gets a new tag, so the two tag orders (hence the commutative operand
     orders) drift for reasons unrelated to the rules. Old against old: 112
     spurious order-only differences in 2 million terms with --batch 5000, none
     when everything is retained (at the price of 1.6 GB for 2 million
     terms). *)
  let retained_old : Old.t list ref = ref []
  let retained_new : New.t list ref = ref []
  let retain_old x = retained_old := x :: !retained_old
  let retain_new x = retained_new := x :: !retained_new

  module OldI =
    Cov.Instrument
      (Old)
      (struct
        let log = old_log
        let retain = retain_old
      end)

  module NewI =
    Cov.Instrument
      (New)
      (struct
        let log = new_log
        let retain = retain_new
      end)

  module OldB = Side.Build (OldI)
  module NewB = Side.Build (NewI)
  module Cmp = Iso.Make (Old) (New)

  type verdict = Agree | Order_only | Diff of string | Both_raise

  let guard f =
    try Ok (f ()) with
    | (Out_of_memory | Stack_overflow) as e -> raise e
    | e -> Error e

  let exn_str e = Printexc.to_string e

  let classify (tm : Tm.t) : verdict =
    old_log := [];
    new_log := [];
    let o = guard (fun () -> OldB.build tm) in
    let n = guard (fun () -> NewB.build tm) in
    match (o, n) with
    | Error _, Error _ -> Both_raise
    | Error e, Ok _ -> Diff ("old raised " ^ exn_str e ^ ", new did not")
    | Ok _, Error e -> Diff ("new raised " ^ exn_str e ^ ", old did not")
    | Ok o, Ok n ->
        if Cmp.iso Iso.Strict o n then Agree
        else if Cmp.iso Iso.Comm o n then Order_only
        else Diff "results differ"

  (** A subterm without a free [Bound] variable can be replayed alone. *)
  let rec closed = function
    | Bound _ -> false
    | Op (Exists1 _, [ ni; _ ]) -> closed ni
    | Op (_, l) -> List.for_all closed l
    | _ -> true

  let children = function
    | Op (Exists1 _, [ ni; body ]) ->
        if closed body then [ ni; body ] else [ ni ]
    | Op (_, l) -> l
    | _ -> []

  let failing = function Agree | Both_raise -> false | _ -> true

  (** The smallest subterm that still fails, descending from the root. *)
  let rec shrink tm =
    match
      List.find_opt (fun c -> closed c && failing (classify c)) (children tm)
    with
    | Some c -> shrink c
    | None -> tm

  (* ------------------------------------------------------------------ *)
  (* Statistics                                                          *)
  (* ------------------------------------------------------------------ *)

  type cov = {
    mutable c_old : int;
    mutable c_new : int;
    mutable c_mismatch : int;
  }

  let cov_tbl : (Cov.key, cov) Hashtbl.t = Hashtbl.create 256

  let cov_get k =
    match Hashtbl.find_opt cov_tbl k with
    | Some c -> c
    | None ->
        let c = { c_old = 0; c_new = 0; c_mismatch = 0 } in
        Hashtbl.add cov_tbl k c;
        c

  let record_coverage () =
    let lo = List.rev !old_log and ln = List.rev !new_log in
    List.iter (fun k -> (cov_get k).c_old <- (cov_get k).c_old + 1) lo;
    List.iter (fun k -> (cov_get k).c_new <- (cov_get k).c_new + 1) ln;
    if List.compare_lengths lo ln = 0 then
      List.iter2
        (fun a b ->
          if a <> b then (
            (cov_get a).c_mismatch <- (cov_get a).c_mismatch + 1;
            (cov_get b).c_mismatch <- (cov_get b).c_mismatch + 1))
        lo ln
    else
      List.iter
        (fun k -> (cov_get k).c_mismatch <- (cov_get k).c_mismatch + 1)
        (lo @ ln)

  type stats = {
    mutable checked : int;
    mutable agree : int;
    mutable order_only : int;
    mutable diffs : int;
    mutable both_raise : int;
    mutable nodes : int;
    reports : (string, int ref * (Tm.t * string) list ref) Hashtbl.t;
  }

  let stats =
    {
      checked = 0;
      agree = 0;
      order_only = 0;
      diffs = 0;
      both_raise = 0;
      nodes = 0;
      reports = Hashtbl.create 16;
    }

  let report_limit = ref 3
  let mode_strict = ref true

  let reset_stats () =
    stats.checked <- 0;
    stats.agree <- 0;
    stats.order_only <- 0;
    stats.diffs <- 0;
    stats.both_raise <- 0;
    stats.nodes <- 0;
    Hashtbl.reset stats.reports;
    Hashtbl.reset cov_tbl

  let describe tm =
    (* old/new pp of [tm], and the verdict, by replaying it *)
    let v = classify tm in
    let o = guard (fun () -> Old.pp (OldB.build tm)) in
    let n = guard (fun () -> New.pp (NewB.build tm)) in
    let s = function Ok s -> s | Error e -> "<raised " ^ exn_str e ^ ">" in
    let kind =
      match v with
      | Agree -> "agree?!"
      | Both_raise -> "both raise"
      | Order_only -> "ORDER-ONLY"
      | Diff r -> "DIFF (" ^ r ^ ")"
    in
    Fmt.str "%s@\n  tm : %a@\n  old: %s@\n  new: %s" kind Tm.pp tm (s o) (s n)

  let sample (tm : Tm.t) =
    stats.checked <- stats.checked + 1;
    stats.nodes <- stats.nodes + Tm.size tm;
    let v = classify tm in
    (match v with
    | Both_raise -> stats.both_raise <- stats.both_raise + 1
    | _ -> record_coverage ());
    match v with
    | Agree -> stats.agree <- stats.agree + 1
    | Both_raise -> ()
    | Order_only | Diff _ ->
        let is_diff = match v with Diff _ -> true | _ -> false in
        if is_diff then stats.diffs <- stats.diffs + 1
        else stats.order_only <- stats.order_only + 1;
        if is_diff || !mode_strict then begin
          let m = shrink tm in
          let key =
            Fmt.str "%s %s"
              (if is_diff then "DIFF" else "ORDER-ONLY")
              (match m with Op (o, _) -> op_name o | _ -> "leaf")
          in
          let cnt, ex =
            match Hashtbl.find_opt stats.reports key with
            | Some x -> x
            | None ->
                let x = (ref 0, ref []) in
                Hashtbl.add stats.reports key x;
                x
          in
          incr cnt;
          if List.length !ex < !report_limit then ex := (m, describe m) :: !ex
        end

  let batch_end () =
    Cmp.clear ();
    retained_old := [];
    retained_new := []

  (* ------------------------------------------------------------------ *)
  (* Output                                                              *)
  (* ------------------------------------------------------------------ *)

  let print_report () =
    let keys =
      Hashtbl.fold (fun k v acc -> (k, v) :: acc) stats.reports []
      |> List.sort compare
    in
    List.iter
      (fun (k, (cnt, ex)) ->
        Fmt.pr "@\n== %s: %d occurrence(s); minimal reproduction(s):@\n" k !cnt;
        List.iter (fun (_, d) -> Fmt.pr "- %s@\n" d) (List.rev !ex))
      keys

  let print_coverage ~full =
    let rows =
      Hashtbl.fold (fun k c acc -> (k, c) :: acc) cov_tbl []
      |> List.sort compare
    in
    Fmt.pr
      "@\n\
       coverage: (entry point, result shape): calls old / calls new / shape \
       disagreements@\n";
    List.iter
      (fun ((e, s), c) ->
        if full || c.c_mismatch > 0 then
          Fmt.pr "  %-22s %-24s %9d %9d %6d@\n" e s c.c_old c.c_new c.c_mismatch)
      rows;
    if not full then Fmt.pr "  (rows without disagreement: use --coverage)@\n";
    let seen = Hashtbl.create 64 in
    Hashtbl.iter (fun (e, _) _ -> Hashtbl.replace seen e ()) cov_tbl;
    let names =
      "exists_1"
      :: List.map (fun (o, _) -> op_name o) (Lazy.force Exhaustive.catalogue)
      |> List.sort_uniq compare
    in
    let missing = List.filter (fun n -> not (Hashtbl.mem seen n)) names in
    Fmt.pr "entry points never called: %s@\n"
      (if missing = [] then "none" else String.concat ", " missing);
    let total_mis = Hashtbl.fold (fun _ c a -> a + c.c_mismatch) cov_tbl 0 in
    Fmt.pr "(entry, shape) rows: %d; call-by-call shape disagreements: %d@\n"
      (List.length rows) total_mis

  let print_summary label =
    Fmt.pr
      "@\n\
       %s [new side: %s%s]@\n\
      \  terms checked : %d (%d nodes)@\n\
      \  identical (STRICT) : %d@\n\
      \  order-only diffs   : %d (equal up to operand order of commutative \
       nodes)@\n\
      \  diffs              : %d@\n\
      \  both sides raised  : %d@\n\
      \  peak heap          : %d MB@\n"
      label New.label
      (if New.available then "" else "; NOT bv_new")
      stats.checked stats.nodes stats.agree stats.order_only stats.diffs
      stats.both_raise
      ((Gc.quick_stat ()).top_heap_words * (Sys.word_size / 8) / 1_048_576)

  (* ------------------------------------------------------------------ *)
  (* Drivers                                                             *)
  (* ------------------------------------------------------------------ *)

  let run_random ~n ~seed ~batch ~quiet =
    let rs = Random.State.make [| seed |] in
    for i = 1 to n do
      sample (Gen.gen_root rs);
      if batch > 0 && i mod batch = 0 then batch_end ();
      if (not quiet) && i mod max 1 (n / 10) = 0 then
        Fmt.epr "  %d/%d (diffs %d, order-only %d)@." i n stats.diffs
          stats.order_only
    done;
    batch_end ()

  let run_exhaustive ~batch =
    let i = ref 0 in
    Exhaustive.iter (fun tm ->
        sample tm;
        incr i;
        if batch > 0 && !i mod batch = 0 then batch_end ());
    batch_end ()

  let failed ~allow_order_only =
    stats.diffs > 0
    || ((not allow_order_only) && !mode_strict && stats.order_only > 0)

  (** Each mutation must be detected; the unmutated run must be clean. *)
  let self_test ~n ~seed =
    let ok = ref true in
    mode_strict := true;
    let run label =
      reset_stats ();
      run_random ~n ~seed ~batch:0 ~quiet:true;
      Fmt.pr "  %-20s checked=%d identical=%d order-only=%d diffs=%d@." label
        stats.checked stats.agree stats.order_only stats.diffs
    in
    Fmt.pr "self-test (%d random terms each, seed %d):@." n seed;
    Config.mutation := Config.No_mutation;
    run "no mutation";
    if stats.diffs > 0 || stats.order_only > 0 then (
      ok := false;
      Fmt.pr "    FAIL: the unmutated stand-in is not clean@.");
    List.iter
      (fun (name, m) ->
        Config.mutation := m;
        run name;
        let detected =
          if m = Config.View_swap_add then
            stats.order_only > 0 && stats.diffs = 0
          else stats.diffs > 0
        in
        Fmt.pr "    %s@." (if detected then "detected" else "NOT DETECTED");
        if not detected then ok := false)
      Config.all;
    Config.mutation := Config.No_mutation;
    Fmt.pr "self-test: %s@." (if !ok then "PASS" else "FAIL");
    if !ok then 0 else 1

  let main () =
    let n = ref 100_000
    and seed = ref 0
    and mode = ref "strict"
    and allow_order_only = ref false
    and self = ref false
    and batch = ref 0
    and full_cov = ref false
    and quiet = ref false
    and positional = ref 0 in
    let rec parse = function
      | [] -> ()
      | "--mode" :: m :: r ->
          mode := m;
          parse r
      | "--allow-order-only" :: r ->
          allow_order_only := true;
          parse r
      | "--mutate" :: name :: r ->
          (match List.assoc_opt name Config.all with
          | Some m -> Config.mutation := m
          | None ->
              Fmt.epr "unknown mutation %s; known: %s@." name
                (String.concat ", " (List.map fst Config.all));
              exit 2);
          parse r
      | "--new" :: _ :: r -> parse r
      | "--self-test" :: r ->
          self := true;
          parse r
      | "--report" :: k :: r ->
          report_limit := int_of_string k;
          parse r
      | "--batch" :: k :: r ->
          batch := int_of_string k;
          parse r
      | "--coverage" :: r ->
          full_cov := true;
          parse r
      | "--quiet" :: r ->
          quiet := true;
          parse r
      | x :: r when String.length x > 0 && x.[0] <> '-' ->
          (match !positional with
          | 0 -> n := int_of_string x
          | 1 -> seed := int_of_string x
          | _ -> failwith "too many positional arguments");
          incr positional;
          parse r
      | x :: _ ->
          Fmt.epr "unknown argument %s@." x;
          exit 2
    in
    parse (List.tl (Array.to_list Sys.argv));
    if !self then exit (self_test ~n:!n ~seed:!seed);
    mode_strict := !mode <> "comm";
    (match !mode with
    | "strict" | "comm" ->
        run_random ~n:!n ~seed:!seed ~batch:!batch ~quiet:!quiet
    | "exhaustive" ->
        Fmt.epr "exhaustive set: %d terms@." (Exhaustive.count ());
        run_exhaustive ~batch:!batch
    | m ->
        Fmt.epr "unknown mode %s@." m;
        exit 2);
    print_summary
      (Fmt.str "mode %s%s, mutation %s" !mode
         (if !mode = "exhaustive" then ""
          else Fmt.str ", N=%d, seed %d" !n !seed)
         (match
            List.find_opt (fun (_, m) -> m = !Config.mutation) Config.all
          with
         | Some (nm, _) -> nm
         | None -> "none"));
    print_report ();
    print_coverage ~full:!full_cov;
    exit (if failed ~allow_order_only:!allow_order_only then 1 else 0)
end

let () =
  let rec which = function
    | "--new" :: "standin" :: _ -> `Standin
    | "--new" :: "real" :: _ -> `Real
    | "--new" :: x :: _ ->
        Fmt.epr "--new: expected real or standin, got %s@." x;
        exit 2
    | _ :: r -> which r
    | [] -> `Real
  in
  match which (Array.to_list Sys.argv) with
  | `Standin ->
      let module R = Run (struct
        include Standin
      end) in
      R.main ()
  | `Real ->
      let module R = Run (struct
        include New_side
      end) in
      R.main ()
