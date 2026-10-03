(* The mutation that is active in the mutated copy of the rules; 0: none *)
let current = ref 0
let on k = !current = k
