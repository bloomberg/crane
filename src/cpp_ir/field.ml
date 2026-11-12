(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Struct members ({!Grammar.Field}), with the families only a member
    names. *)

include Grammar.Field
module Method = Grammar.Method
module Receiver = Grammar.Receiver
module Constructor = Grammar.Constructor
module Deferred_struct = Grammar.Deferred_struct
module Out_of_line = Grammar.Out_of_line
module Visibility = Grammar.Visibility
module Section = Grammar.Section
