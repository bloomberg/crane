(** Control: the same solver through stock OCaml extraction, but with the
    tree erased by hand the way Crane erases it -- [itree E R] is [R],
    [bind] is application, and each event is a direct call.  Unsound in
    general (it is only right because every event here is a total, in-order
    effect), but it separates what the tree costs from what OCaml costs. *)
From Stdlib Require Import Extraction.
Require Import OcamlNat SatVec Solver.
From Crane Require Import Monads.ITree.
Extract Inductive vec => "Vec_impl.t" [ "(fun _ -> assert false)" ].
Extract Inductive itree => "Direct.t" [ "Direct.go" ].
Extract Inlined Constant observe => "Direct.observe".
Extract Inlined Constant Ret => "(fun x -> x)".
Extract Inlined Constant ITree.bind => "(fun m k -> k m)".
Extract Inlined Constant vmake => "(fun _ n x -> Vec_impl.make n x)".
Extract Inlined Constant vget => "(fun _ v i -> Vec_impl.get v i)".
Extract Inlined Constant vset => "(fun _ v i x -> Vec_impl.set v i x)".
Extract Inlined Constant vlen => "(fun _ v -> Vec_impl.len v)".
Extract Inlined Constant vpush => "(fun _ v x -> Vec_impl.push v x)".
Extract Inlined Constant vshrink => "(fun _ v n -> Vec_impl.shrink v n)".
Extract Inlined Constant vabort => "(fun _ site -> Vec_impl.abort site)".
Extraction "solver_direct_ml.ml" Solver.solve.
