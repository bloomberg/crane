
(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

module Nat =
 struct
  (** val sub : int -> int -> int **)

  let rec sub = fun n m -> Stdlib.max 0 (n-m)

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (Stdlib.Int.succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val modulo : int -> int -> int **)

  let modulo = fun n m -> if m = 0 then n else n mod m
 end

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun len0 -> start :: (seq (Stdlib.Int.succ start) len0))
    len

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: l0 -> fold_left f l0 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: l0 -> f b (fold_right f a0 l0)

module GbClo =
 struct
  (** val compose : (int -> int) -> (int -> int) -> int -> int **)

  let compose f g x =
    f (g x)

  (** val build : int -> (int -> int) list **)

  let rec build n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> [])
      (fun m -> (fun x ->
      Nat.modulo
        (add (mul x (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
          n)
        4093) :: (build m))
      n

  (** val closures : int -> int -> int **)

  let closures n rounds =
    let fs = build n in
    let big = fold_right compose (fun x -> x) fs in
    fold_left (fun acc i ->
      add (add acc (big i)) (fold_left (fun a f -> f a) fs i)) (seq 0 rounds)
      0
 end
