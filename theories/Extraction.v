(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Main entry point for the Crane extraction plugin.

   Importing this module loads the plugin and makes the [Crane Extraction]
   vernacular commands available. Most user files should begin with:
   [From Crane Require Extraction.]
*)
Declare ML Module "rocq-crane.plugin".

(** The digest of the C++ runtime headers: a file that loads Crane depends
    on their contents, so an image [Crane Bake] computed from old headers is
    rebuilt (docs/Crane-Bake.md). *)
Require Crane.RuntimeHeaders.
