# Standalone Rust value language (stage S5a)

soteria-rust's values, written in Kanon: the language `Rust` is generated from
the SHARED modules of Bv_values (bool, exists, bitvec, float, ptr and the `view`
of the host code) plus the `rust` module (aggregates, thin/full pointers,
pointer metadata, poly values), over the same generic host stack as C
(`Lang_v.Make`, `Typed_v.Make_transparent`). soteria-rust itself is NOT changed:
this directory is the analogue of what `bv_new` was for C. The cut-over is a
later stage.

## Layout

| file | content |
|---|---|
| `rules/lang.knl` | the language: the shared modules (their path is written ONLY here), `Var`, `Seq`, host types, ghost tags (`sptr_f sptr_t tuple enum union poly scalar aggregate any`) |
| `rules/rust.knl`, `rules/rust.kn` | host types, sorts `TEnum TUnion TTuple TArray TThinPtr TFullPtr TPtrMeta TPolyType`, leaf nodes `ThinPtr FullPtr PtrMeta Enum Tuple Array Union PolyVal ThinPtrPart FullPtrInner FullPtrMeta PtrMetaAs Field VariantField IsVariant ArrayField`; the smart constructors of `ext_base.ml` as Kanon `fn`s; the `extend fn` cases of the view (`operands rebuild node_cost cost learn_alts learn_value sort_operands encode_sort encode_head pp_style`). Everything is `[@no_lean]`: there is no Lean semantics for these nodes. `[@total]` makes Kanon reject a node without a case (checked: removing `ArrayField` from `encode_head` gives `fn encode_head is [@total] but has no case for ArrayField`) |
| `rust_types.gen.ml`, `rust_rules.gen.ml` | generated, committed (`regen.sh [KANON]`; in `.ocamlformat-ignore`) |
| `base_prims.ml`, `base_view_prims.ml` | COPIES of `bv_prims.ml`/`view_prims.ml` of the C language over `Rust_types`; 3 patches marked `PATCH`: `rust_operands` + a case in `used_binders_iter_vars`, and `pp_ty` printing the Rust sorts as `(TExtension X)` like the old derived printer |
| `rust_host.ml`, `rust_charon.ml`, `rust_encoding.ml`, `rust_prims.ml` | `ptag`; `ty_of_rust`, `usize_bits`, `t_as_*` (ext_base.ml); the SMT sort modules and operators (encoding.ml, same text, same order of `encode_child`/declarations); the prims of rust.kn (crate reads, exceptions of the old code, `ph_*` text heads) |
| `rust_lang.ml`, `rust_stack.ml`, `rust_typed.ml(i)` | `Kanon_fns` composition; `Lang_v.Make`; port of `lib/svalue/typed.ml` (+ the interface, same as `typed.mli` except the head) |
| `iface.ml` | the ONE file naming the generic stack (`Soteria.Bv_values.*`) |
| `golden_new/` | `golden.ml` with only the `Ty` alias changed |
| `diff/` | differential test old vs new; `diff/mut/` the mutants of its self-test |
| `bench/` | arrays: old `Iarray` vs new lists |

## Running

```sh
dune build soteria-rust/test/rust_new
dune test soteria-rust/test/rust_new     # golden diff + 20 chunks + self-test, ~4 s
rust_new/diff/rust_diff.exe --chunks 2000 --n 100   # ~6 min, 11.5M lines compared
rust_new/bench/bench.exe 4096
./regen.sh /path/to/new/kanon            # needs the NEW kanon (computed sorts, [@total])
```
`golden_new` output must be byte-identical to `../golden/golden.expected`.

## Differential test (`diff/`)

`body.ml` is the generator/observer of the golden (same shapes, ops, synthetic
crate) run on a stack chosen by a prelude (`old_side.ml`, `new_side.ml`,
`mut_side.ml` = prelude + body). Every value is printed through a neutral AST
(`neutral.ml`; `old_conv.ml`/`new_conv.ml` match each stack's own constructors)
so structure, parameters, sorts and operand ORDER (strict) are compared, plus
`pp`, `pp_ty`, cost, eval, subst, learn, `map_operands`, SMT text with
declaration order, and exceptions. Pointer tags come from a pool shared by
both stacks. GC is off inside a chunk (weak tables: a recreated node would
change tags and operand order; false differences otherwise).
`--self-test` compares the old stack with 10 mutants of the generated rules
(`mutations.ml`) and with the unmutated copy; all must be detected / agree.

## Deviations

- Thin pointer and block record fields are renamed (`ptag psize palign`,
  `bvalue boffset bsize`) to avoid clashes inside the generated type group; the
  typed interface keeps the old polymorphic `block_raw` and converts.
- `Iarray` -> `t list` in `Array` (no Kanon equivalent); conversions in
  `Typed.Adt.mk_array/as_array`.
- Old `Ptr` of Rust is `FullPtr`. Sorts print as `(TExtension X)` as before.
- `Rust_stack.K` is sealed as `Kanon_fns`; Rust code uses `Rust_lang` directly.

## Risks / not verified

- Arrays as lists (4096 elements, CPU time per call): `array_field_of` last
  element 6.4 us vs 6.5 ns (x990); all elements in turn 13 ms vs 18 us (x700);
  `as_array` of a concrete array 58 us vs 25 ns (O(n) list->Iarray at the
  interface); `mk_array` x1.3; symbolic `as_array`, `set_array_field` and
  `array_field_of` on variables ~equal (x0.6-1.3). Interpreter loops over big
  concrete arrays become quadratic: if it matters, ask Kanon for an array
  container (K10) or keep a side index.
- Crate-dependent prims (`ty_of_rust`, `variant_field_ty`, `usize_bits`) run
  inside what are now Kanon fns; Charon types are hashed by `Hashtbl.hash`, as before.
- No Lean. No end-to-end Rust analysis, no cram tests, no Kani.
- `base_*prims.ml` are copies: replace by the shared prims functor when it exists.
- `(package soteria-rust)` on the runtest rules, with a private dependency on
  Soteria internals: `dune build -p soteria-rust` not tried.

## Work for the cut-over

Move rules/prims into `soteria-rust/lib/svalue`; delete `Ext`, `ext_base`,
`ext.ml`, old `encoding.ml`, `typed.ml`; `rustsymex.ml:21` instantiation; replace
`TExtension X` by `X` at 28 sites (value_codec, builtins/{optim,core,intrinsics,extern},
state/rtree_block) and in `ppx_typed_match.ml` (+ 21 files of test/ppx/ty);
shared prims functor; run cram tests.
