(* Rocq bug #4720: extraction and "with" in module type *)

Require Crane.Extraction.

Module RocqBug4720.

Module Type A.
 Parameter t : Set.
End A.

Module A_instance <: A.
 Definition t := nat.
End A_instance.

Module A_private : A.
 Definition t := nat.
End A_private.

Module Type B.
End B.

Module Type C (b : B).
 Declare Module a : A.
End C.

Module WithMod (a' : A) (b' : B) (c' : C b' with Module a := A_instance).
End WithMod.

Module WithDef (a' : A) (b' : B) (c' : C b' with Definition a.t := nat).
End WithDef.

Module WithModPriv (a' : A) (b' : B) (c' : C b' with Module a := A_private).
End WithModPriv.

End RocqBug4720.

Crane Extraction "rocq_bug_4720" RocqBug4720.
