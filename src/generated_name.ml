(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

let separate_underscores s =
  let b = Buffer.create (String.length s) in
  String.iteri
    (fun i c ->
      Buffer.add_char b
        (if c = '_' && i > 0 && Buffer.nth b (Buffer.length b - 1) = '_'
         then 'p' else c) )
    s;
  Buffer.contents b

let role r =
  assert (r <> "" && Char.uppercase_ascii r.[0] = r.[0] && r.[0] <> '_');
  "Crane" ^ r

let id r = Id.of_string (role r)

let indexed r i = Id.of_string (role r ^ string_of_int i)

let member r ~of_ i = if of_ = 1 then id r else indexed r i

let companion x r =
  Id.of_string (separate_underscores (Id.to_string x ^ "_crane_" ^ r))

let prefixed p x =
  let s = Id.to_string x in
  Id.of_string (if s <> "" && s.[0] = '_' then p ^ s else p ^ "_" ^ s)
