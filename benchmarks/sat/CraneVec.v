(** Crane mappings for [SatVec]: each event is a direct call. *)
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree.
Require Import SatVec.

Crane Extract Inductive vec => "satbench::vec<%t0>" [ "satbench::no_loc<%t0>(%a0)" ] From "sat_vec.h".
Crane Extract Skip vecE.
Crane Extract Inlined Constant vmake => "satbench::make_vec(%a0, %a1)" From "sat_vec.h".
Crane Extract Inlined Constant vget => "%a0.get(%a1)".
Crane Extract Inlined Constant vset => "%a0.set(%a1, %a2)".
Crane Extract Inlined Constant vlen => "%a0.len()".
Crane Extract Inlined Constant vpush => "%a0.push(%a1)".
Crane Extract Inlined Constant vshrink => "%a0.shrink(%a1)".
Crane Extract Inlined Constant vabort => "satbench::abort<%t1>(%a0)" From "sat_vec.h".
