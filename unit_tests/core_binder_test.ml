(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* A Core binder is its definition and level; where it records a site --
   a let or bind, or a match and one of its branches -- the site tells
   apart two binders the scope does not. *)

open Crane_plugin
open Names
open Miniml

let check name cond =
  if not cond then (
    Printf.eprintf "core_binder: %s\n" name;
    exit 1 )

let () =
  let origin = GlobRef.VarRef (Id.of_string "f") in
  let at ?site () = Core_binder.make ~origin ~level:2 ?site () in
  let let_ = Occurrence.fresh () and match_ = Occurrence.fresh () and other = Occurrence.fresh () in
  let bound = at ~site:(Binding let_) () in
  let first = at ~site:(Branch (match_, 0)) () in
  let second = at ~site:(Branch (match_, 1)) () in
  let elsewhere = at ~site:(Branch (other, 0)) () in
  check "one level is one binder in scope" (Core_binder.equal first second && Core_binder.equal bound first);
  check "a branch is its own site" (Core_binder.same_site first (at ~site:(Branch (match_, 0)) ()));
  check "two branches of one match are two sites" (not (Core_binder.same_site first second));
  check "one branch of two matches is two sites" (not (Core_binder.same_site first elsewhere));
  check "a pattern is not a let" (not (Core_binder.same_site bound first || Core_binder.same_site first bound));
  check "a binder recording no site is told apart from none" (Core_binder.same_site (at ()) first && Core_binder.same_site bound (at ()))
