From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From CraneTestsRegression Require Import sep_ext_mutual_template_order.Ty.

(** A mutual group of free functions: the types live in another file, so they
    are not methods.  Each calls the other with explicit template arguments,
    which C++ looks up where the call is written -- so the header declares the
    group before defining it. *)
Fixpoint tmap {A B} (f : A -> B) (t : tree A) : tree B :=
  match t with Node a fs => Node (f a) (fmap f fs) end
with fmap {A B} (f : A -> B) (fs : forest A) : forest B :=
  match fs with Nil => Nil | Cons t r => Cons (tmap f t) (fmap f r) end.
