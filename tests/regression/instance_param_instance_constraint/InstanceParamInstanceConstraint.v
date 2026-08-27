From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
(** An instance parameterised by another instance (`Def A -> Def (option A)`)
    used at `option (option nat)`: the nested instantiation must list the
    instance argument before the type argument, matching the generated
    struct's template parameter order. *)

Module InstanceParamInstanceConstraint.
Class Def (A : Type) := { dflt : A }.
Instance DNat : Def nat := { dflt := 9 }.
Instance DOpt (A : Type) (d : Def A) : Def (option A) := { dflt := Some dflt }.
Definition go : nat := match (dflt : option (option nat)) with
                       | Some (Some n) => n | _ => 0 end.
End InstanceParamInstanceConstraint.
Crane Extraction "instance_param_instance_constraint" InstanceParamInstanceConstraint.
