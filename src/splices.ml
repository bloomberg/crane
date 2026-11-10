(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What splicing decided about loopified functions' partners.  See
    [splices.mli]. *)

open Miniml

type t = { decided : Ref.User.Set.t; entered : Occurrence.t Ref.User.Map.t }

let empty = { decided = Ref.User.Set.empty; entered = Ref.User.Map.empty }

let decide ?entered r s =
  { decided = Ref.User.Set.add r s.decided;
    entered = (match entered with Some o -> Ref.User.Map.add r o s.entered | None -> s.entered) }

let decided s r = Ref.User.Set.mem r s.decided
let entered_copy s r = Ref.User.Map.find_opt r s.entered
let is_entered_copy s o = Ref.User.Map.exists (fun _ o' -> Occurrence.equal o o') s.entered

let equal s s' =
  Ref.User.Set.equal s.decided s'.decided && Ref.User.Map.equal Occurrence.equal s.entered s'.entered
