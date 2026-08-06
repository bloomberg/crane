From Crane Require Extraction.

Variant ex (A : Type) : Type := mk_box.

Crane Extract Inductive ex => "std::monostate"
  [ "std::monostate{}" ]
From "variant".

Definition f {A : Type} (b : ex A) : unit := tt.
