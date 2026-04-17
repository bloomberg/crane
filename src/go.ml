
(** Go extraction back-end entry point.

    Assembles the {!Miniml.language_descr} record for Go and re-exports it
    as [go_descr].  All heavy lifting is in {!Go_print}. *)

open Table
open Miniml
open Common
open Go_print

(** [file_naming mp] returns the base filename (without extension) for the
    Go file generated from module path [mp]. *)
let file_naming mp = String.lowercase_ascii (string_of_modfile mp)

(** The language descriptor for Go extraction. *)
let go_descr : language_descr = {
  keywords     = go_keywords;
  file_suffix  = ".go";
  file_naming;
  preamble     = pp_go_preamble;
  pp_struct         = pp_go_struct;
  pp_hstruct        = pp_go_hstruct;
  skip_empty_files  = true;
  sig_suffix        = None;
  sig_preamble = pp_go_sig_preamble;
  pp_sig       = pp_go_sig;
  pp_decl      = pp_go_decl;
}
