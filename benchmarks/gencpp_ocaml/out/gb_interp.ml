
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

(** val hd : 'a1 -> 'a1 list -> 'a1 **)

let hd default = function
| [] -> default
| x :: _ -> x

(** val tl : 'a1 list -> 'a1 list **)

let tl = function
| [] -> []
| _ :: l' -> l'

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: l0 -> fold_left f l0 (f a0 b)

module GbInterp =
 struct
  (** val next : int -> int **)

  let next s =
    Nat.modulo
      (add
        (mul s (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ
        0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      65537

  type expr =
  | Num of int
  | Var of int
  | Add of expr * expr
  | Mul of expr * expr
  | Let of expr * expr
  | If0 of expr * expr * expr

  (** val lookup : int list -> int -> int **)

  let rec lookup env i =
    match env with
    | [] -> 0
    | v :: r ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ -> v)
         (fun j -> lookup r j)
         i)

  (** val eval : int list -> expr -> int **)

  let rec eval env = function
  | Num n -> n
  | Var i -> lookup env i
  | Add (a, b) -> Nat.modulo (add (eval env a) (eval env b)) 4096
  | Mul (a, b) -> Nat.modulo (mul (eval env a) (eval env b)) 4096
  | Let (d, body) -> eval ((eval env d) :: env) body
  | If0 (c, t, f) -> if (=) (eval env c) 0 then eval env t else eval env f

  (** val is_num : int -> expr -> bool **)

  let is_num n = function
  | Num m -> (=) m n
  | _ -> false

  (** val sadd : expr -> expr -> expr **)

  let sadd a b =
    if is_num 0 a
    then b
    else if is_num 0 b
         then a
         else (match a with
               | Num x ->
                 (match b with
                  | Num y -> Num (Nat.modulo (add x y) 4096)
                  | _ -> Add (a, b))
               | _ -> Add (a, b))

  (** val smul : expr -> expr -> expr **)

  let smul a b =
    if is_num (Stdlib.Int.succ 0) a
    then b
    else if is_num (Stdlib.Int.succ 0) b then a else Mul (a, b)

  (** val simplify : expr -> expr **)

  let rec simplify e = match e with
  | Add (a, b) -> sadd (simplify a) (simplify b)
  | Mul (a, b) -> smul (simplify a) (simplify b)
  | Let (d, body) -> Let ((simplify d), (simplify body))
  | If0 (c, t, f) -> If0 ((simplify c), (simplify t), (simplify f))
  | _ -> e

  type instr =
  | IPush of int
  | ILoad of int
  | IAdd
  | IMul
  | IBind
  | IUnbind

  (** val compile : expr -> instr list -> instr list **)

  let rec compile e k =
    match e with
    | Num n -> (IPush n) :: k
    | Var i -> (ILoad i) :: k
    | Add (a, b) -> compile a (compile b (IAdd :: k))
    | Mul (a, b) -> compile a (compile b (IMul :: k))
    | Let (d, body) -> compile d (IBind :: (compile body (IUnbind :: k)))
    | If0 (_, t, _) -> compile t k

  (** val binop : (int -> int -> int) -> int list -> int list **)

  let binop op s = match s with
  | [] -> s
  | b :: l -> (match l with
               | [] -> s
               | a :: r -> (op a b) :: r)

  (** val run : int -> instr list -> int list -> int list -> int **)

  let rec run fuel code stack env =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun f ->
      match code with
      | [] -> hd 0 stack
      | i0 :: c ->
        (match i0 with
         | IPush n -> run f c (n :: stack) env
         | ILoad i -> run f c ((lookup env i) :: stack) env
         | IAdd ->
           run f c (binop (fun a b -> Nat.modulo (add a b) 4096) stack) env
         | IMul ->
           run f c (binop (fun a b -> Nat.modulo (mul a b) 4096) stack) env
         | IBind -> run f c (tl stack) ((hd 0 stack) :: env)
         | IUnbind -> run f c stack (tl env)))
      fuel

  (** val gen : int -> int -> expr **)

  let rec gen depth s =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      if (=)
           (Nat.modulo s (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             0))))
           0
      then Var
             (Nat.modulo s (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
               (Stdlib.Int.succ 0)))))
      else Num
             (Nat.modulo s (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
               (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
               (Stdlib.Int.succ 0)))))))))
      (fun d ->
      let s' = next s in
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ -> Add ((gen d s'), (gen d (next s'))))
         (fun n ->
         (fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ -> Mul ((gen d s'), (Num (Stdlib.Int.succ 0))))
           (fun n0 ->
           (fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ -> Let ((gen d s'), (gen d (next s'))))
             (fun n1 ->
             (fun fO fS n -> if n=0 then fO () else fS (n-1))
               (fun _ -> If0 ((gen d s'), (gen d (next s')), (Num
               0)))
               (fun _ -> Add ((Num 0), (gen d s')))
               n1)
             n0)
           n)
         (Nat.modulo s (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
      depth

  (** val round : int -> int -> int **)

  let round depth i =
    let e =
      gen depth
        (add i (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
    in
    let e' = simplify e in
    add
      (add
        (eval ((Stdlib.Int.succ 0) :: ((Stdlib.Int.succ (Stdlib.Int.succ
          0)) :: ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          0))) :: ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ 0)))) :: [])))) e)
        (eval ((Stdlib.Int.succ 0) :: ((Stdlib.Int.succ (Stdlib.Int.succ
          0)) :: ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          0))) :: ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ 0)))) :: [])))) e'))
      (run 100000000 (compile e' []) [] ((Stdlib.Int.succ
        0) :: ((Stdlib.Int.succ (Stdlib.Int.succ 0)) :: ((Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))) :: ((Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))) :: [])))))

  (** val interp : int -> int -> int **)

  let interp depth rounds =
    fold_left (fun acc i -> add acc (round depth i)) (seq 0 rounds) 0
 end
