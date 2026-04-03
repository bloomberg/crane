(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   STM (Software Transactional Memory) effect events for the standard
   library flavor.

   Re-exports shared definitions from [STMDefs.v] and adds C++ extraction
   mappings targeting the standard library.
*)
From Crane Require Extraction.
From Crane Require Import Mapping.Std Monads.IO External.Vector.
From Crane Require Export Monads.STMDefs.

Crane Extract Inductive tvarE => ""
  [ "stm::newTVar(%a0)" "%a0->read()" "%a0->write(%a1)" ]
  From "mini_stm.h".

Crane Extract Inlined Constant TVar => "std::shared_ptr<stm::TVar<%t0>>" From "mini_stm.h".

Crane Extract Inlined Constant readTVar => "%a0->read()".
Crane Extract Inlined Constant writeTVar => "%a0->write(%a1)".
