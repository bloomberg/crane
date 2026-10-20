(* Growable arrays backing [vecE] on the OCaml side. *)
type 'a t = { mutable data : 'a array; mutable len : int }

let make n x = { data = Array.make (max n 1) x; len = n }
let get v i = Array.unsafe_get v.data i
let set v i x = Array.unsafe_set v.data i x
let len v = v.len

let push v x =
  if v.len = Array.length v.data then begin
    let d = Array.make (2 * v.len + 1) x in
    Array.blit v.data 0 d 0 v.len;
    v.data <- d
  end;
  Array.unsafe_set v.data v.len x;
  v.len <- v.len + 1

let shrink v n = if n < v.len then v.len <- n
