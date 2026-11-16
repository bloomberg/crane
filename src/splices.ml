(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What splicing decided about loopified functions' partners.  See
    [splices.mli]. *)


type t = { decided : Core.Ref.User.Set.t; entered : Core.Occurrence.t Core.Ref.User.Map.t }

let empty = { decided = Core.Ref.User.Set.empty; entered = Core.Ref.User.Map.empty }

let decide ?entered r s =
  { decided = Core.Ref.User.Set.add r s.decided;
    entered = (match entered with Some o -> Core.Ref.User.Map.add r o s.entered | None -> s.entered) }

let decided s r = Core.Ref.User.Set.mem r s.decided
let entered_copy s r = Core.Ref.User.Map.find_opt r s.entered
let is_entered_copy s o = Core.Ref.User.Map.exists (fun _ o' -> Core.Occurrence.equal o o') s.entered

let equal s s' =
  Core.Ref.User.Set.equal s.decided s'.decided && Core.Ref.User.Map.equal Core.Occurrence.equal s.entered s'.entered
