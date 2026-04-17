(** Standard-library extraction mappings for the Go backend.

    Maps [bool], [unit], [option], [prod], [list], [nat], [positive],
    [PrimInt63], [PrimFloat], and [PrimString] to their idiomatic Go
    equivalents.  Sets the extraction language to Go. *)
From Crane Require Extraction.

Crane Extraction Language Go.

(* ------------------------------------------------------------------ *)
(** Bool *)
(* ------------------------------------------------------------------ *)

Crane Extract Inductive bool =>
  "bool"
  [ "true" "false" ]
  "func() any { if %scrut { return %br0 } else { return %br1 } }()".

Crane Extract Inlined Constant negb => "!(%a0)".
Crane Extract Inlined Constant andb => "(%a0 && %a1)".
Crane Extract Inlined Constant orb  => "(%a0 || %a1)".

(* ------------------------------------------------------------------ *)
(** Unit *)
(* ------------------------------------------------------------------ *)

Crane Extract Inductive unit =>
  "struct{}"
  [ "struct{}{}" ]
  "func() any { %br0 }()".

(* ------------------------------------------------------------------ *)
(** Option *)
(* ------------------------------------------------------------------ *)

Crane Extract Inductive option =>
  "*%t0"
  [ "rocqSome(%a0)" "nil" ]
  "func() any { if %scrut != nil { %b0a0 := %scrut; return %br0 } else { return %br1 } }()".

(* ------------------------------------------------------------------ *)
(** Prod (pair) *)
(* ------------------------------------------------------------------ *)

Crane Extract Inductive prod =>
  "struct{ fst %t0; snd %t1 }"
  [ "struct{ fst %t0; snd %t1 }{fst: %a0, snd: %a1}" ]
  "func() any { %b0a0 := %scrut.fst; %b0a1 := %scrut.snd; return %br0 }()".

Crane Extract Inlined Constant fst => "%a0.fst".
Crane Extract Inlined Constant snd => "%a0.snd".

(* ------------------------------------------------------------------ *)
(** Int63 primitives → int64 with 63-bit masking *)
(* ------------------------------------------------------------------ *)
From Corelib Require Import PrimInt63.
Crane Extract Inlined Constant PrimInt63.int => "int64".
Crane Extract Inlined Constant PrimInt63.add => "((%a0 + %a1) & 0x7FFFFFFFFFFFFFFF)".
Crane Extract Inlined Constant PrimInt63.sub => "((%a0 - %a1) & 0x7FFFFFFFFFFFFFFF)".
Crane Extract Inlined Constant PrimInt63.mul => "((%a0 * %a1) & 0x7FFFFFFFFFFFFFFF)".
Crane Extract Inlined Constant PrimInt63.div => "func() int64 { if %a1 == 0 { return 0 }; return %a0 / %a1 }()".
Crane Extract Inlined Constant PrimInt63.mod => "func() int64 { if %a1 == 0 { return 0 }; return %a0 %% %a1 }()".
Crane Extract Inlined Constant PrimInt63.eqb => "(%a0 == %a1)".
Crane Extract Inlined Constant PrimInt63.ltb => "(%a0 < %a1)".
Crane Extract Inlined Constant PrimInt63.leb => "(%a0 <= %a1)".
Crane Extract Inlined Constant PrimInt63.land => "(%a0 & %a1)".
Crane Extract Inlined Constant PrimInt63.lor  => "(%a0 | %a1)".
Crane Extract Inlined Constant PrimInt63.lxor => "(%a0 ^ %a1)".
Crane Extract Inlined Constant PrimInt63.lsl  =>
  "func() int64 { if %a1 >= 63 { return 0 }; return (%a0 << uint(%a1)) & 0x7FFFFFFFFFFFFFFF }()".
Crane Extract Inlined Constant PrimInt63.lsr  =>
  "func() int64 { if %a1 >= 63 { return 0 }; return %a0 >> uint(%a1) }()".

(* ------------------------------------------------------------------ *)
(** Float → float64 *)
(* ------------------------------------------------------------------ *)
From Corelib Require Import PrimFloat.
Crane Extract Inlined Constant PrimFloat.float  => "float64".
Crane Extract Inlined Constant PrimFloat.add    => "(%a0 + %a1)".
Crane Extract Inlined Constant PrimFloat.sub    => "(%a0 - %a1)".
Crane Extract Inlined Constant PrimFloat.mul    => "(%a0 * %a1)".
Crane Extract Inlined Constant PrimFloat.div    => "(%a0 / %a1)".
Crane Extract Inlined Constant PrimFloat.opp    => "(-%a0)".
Crane Extract Inlined Constant PrimFloat.abs    => "math.Abs(%a0)".
Crane Extract Inlined Constant PrimFloat.sqrt   => "math.Sqrt(%a0)".
Crane Extract Inlined Constant PrimFloat.eqb    => "(%a0 == %a1)".
Crane Extract Inlined Constant PrimFloat.ltb    => "(%a0 < %a1)".
Crane Extract Inlined Constant PrimFloat.leb    => "(%a0 <= %a1)".
Crane Extract Inlined Constant PrimFloat.of_uint63 => "float64(%a0)".

(* ------------------------------------------------------------------ *)
(** PrimString → string *)
(* ------------------------------------------------------------------ *)
From Corelib Require Import PrimString.
Crane Extract Inlined Constant PrimString.char63  => "byte".
Crane Extract Inlined Constant PrimString.string  => "string".
Crane Extract Inlined Constant PrimString.cat     => "(%a0 + %a1)".
Crane Extract Inlined Constant PrimString.get     => "%a0[%a1]".
Crane Extract Inlined Constant PrimString.sub     => "%a0[%a1:%a1+%a2]".
Crane Extract Inlined Constant PrimString.length  => "int64(len(%a0))".
