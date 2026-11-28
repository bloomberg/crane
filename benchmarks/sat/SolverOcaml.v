(** Stock OCaml extraction of [Solver], as imperative as the C++ Crane
    makes of it.  The tree is erased the way Crane erases it: [itree E R]
    is [R], [bind] is application, and every [Global] operation is a direct
    call on an OCaml array or reference ([sat_rt.ml]).  [nat] is a native
    [int], as in the C++.  This is only right because every event of the
    solver is a total, in-order effect, which is what Crane assumes too. *)
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt PeanoNat.
From Crane Require Import Monads.ITree Monads.Global.
Require Import Solver.

(** Native-int realizers for the [nat] operations the solver uses. *)
Extract Inlined Constant Nat.add => "(+)".
Extract Inlined Constant Nat.sub => "(fun a b -> if a > b then a - b else 0)".
Extract Inlined Constant Nat.mul => "( * )".
Extract Inlined Constant Nat.div => "(fun a b -> if b = 0 then 0 else a / b)".
Extract Inlined Constant Nat.modulo => "(fun a b -> if b = 0 then a else a mod b)".
Extract Inlined Constant Nat.eqb => "(=)".
Extract Inlined Constant Nat.leb => "(<=)".
Extract Inlined Constant Nat.ltb => "(<)".
Extract Inlined Constant Nat.max => "(fun a b -> if a < b then b else a)".

(** The erased tree. *)
Extract Inductive itree => "Sat_rt.t" [ "Sat_rt.go" ].
Extract Inlined Constant observe => "Sat_rt.observe".
Extract Inlined Constant Ret => "(fun x -> x)".
Extract Inlined Constant ITree.bind => "(fun m k -> k m)".

(** Arrays and references. *)
Extract Inductive Global.array => "Sat_rt.array" [ "(fun _ _ -> assert false)" ].
Extract Inlined Constant Global.new_array => "(fun _ _ _ n x -> Array.make n x)".
Extract Inlined Constant Global.read_array => "(fun _ _ _ a i -> Array.unsafe_get a i)".
Extract Inlined Constant Global.write_array => "(fun _ _ _ a i x -> Array.unsafe_set a i x)".
Extract Inlined Constant Global.swap_array => "(fun _ _ _ a i j -> Sat_rt.swap a i j)".
Extract Inlined Constant Global.new_ref => "(fun _ _ _ x -> Obj.repr (ref x))".
Extract Inlined Constant Global.read_ref => "(fun _ _ _ r -> !(Obj.obj r))".
Extract Inlined Constant Global.write_ref => "(fun _ _ _ r x -> Obj.obj r := x)".
Extract Inlined Constant Solver.out_of_fuel => "(raise Sat_rt.Out_of_fuel)".
(** Only the type of [out_of_fuel]'s message is left of [Err]. *)
Extract Constant PrimString.string => "Stdlib.String.t".

Extraction "solver_ml.ml" Solver.solve_dimacs.
