(** Workloads for measuring the C++ Crane generates: persistent trees, list
    pipelines, an interpreter, closures and a balanced map from the standard
    library.  Each entry point folds its result into one number. *)
From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Stdlib Require Import List PeanoNat FMapAVL OrderedTypeEx.
Require Import Crane.Mapping.NatInt.
Require Crane.Extraction.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.
Import ListNotations.

Module GbInterp.

(** Moduli and fuel, given as C++ literals: a closed [nat] product would be
    reduced to a unary numeral during extraction. *)
Axiom m_lcg m_sum m_clo m_val m_key m_map fuel_big : nat.

(** Pseudo-random numbers: a linear congruential step of the ZX81, kept below 65537. *)
Definition next (s : nat) : nat := (s * 75 + 74) mod m_lcg.

Fixpoint randoms (n s : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => s :: randoms n' (next s)
  end.

(** A small expression language: evaluation with an environment, constant
    folding, and compilation to a stack machine that is then run. *)
Inductive expr :=
| Num (n : nat)
| Var (i : nat)
| Add (a b : expr)
| Mul (a b : expr)
| Let (e body : expr)
| If0 (c t e : expr).

Fixpoint lookup (env : list nat) (i : nat) : nat :=
  match env, i with
  | [], _ => 0
  | v :: _, 0 => v
  | _ :: r, S j => lookup r j
  end.

Fixpoint eval (env : list nat) (e : expr) : nat :=
  match e with
  | Num n => n
  | Var i => lookup env i
  | Add a b => (eval env a + eval env b) mod m_val
  | Mul a b => (eval env a * eval env b) mod m_val
  | Let d body => eval (eval env d :: env) body
  | If0 c t f => if eval env c =? 0 then eval env t else eval env f
  end.

Definition is_num (n : nat) (e : expr) : bool :=
  match e with Num m => m =? n | _ => false end.

Definition sadd (a b : expr) : expr :=
  if is_num 0 a then b
  else if is_num 0 b then a
  else match a, b with
       | Num x, Num y => Num ((x + y) mod m_val)
       | _, _ => Add a b
       end.

Definition smul (a b : expr) : expr :=
  if is_num 1 a then b else if is_num 1 b then a else Mul a b.

Fixpoint simplify (e : expr) : expr :=
  match e with
  | Add a b => sadd (simplify a) (simplify b)
  | Mul a b => smul (simplify a) (simplify b)
  | Let d body => Let (simplify d) (simplify body)
  | If0 c t f => If0 (simplify c) (simplify t) (simplify f)
  | e => e
  end.

Inductive instr := IPush (n : nat) | ILoad (i : nat) | IAdd | IMul | IBind | IUnbind.

Fixpoint compile (e : expr) (k : list instr) : list instr :=
  match e with
  | Num n => IPush n :: k
  | Var i => ILoad i :: k
  | Add a b => compile a (compile b (IAdd :: k))
  | Mul a b => compile a (compile b (IMul :: k))
  | Let d body => compile d (IBind :: compile body (IUnbind :: k))
  | If0 c t f => compile t k
  end.

Definition binop (op : nat -> nat -> nat) (s : list nat) : list nat :=
  match s with
  | b :: a :: r => op a b :: r
  | _ => s
  end.

Fixpoint run (fuel : nat) (code : list instr) (stack env : list nat) : nat :=
  match fuel with
  | 0 => 0
  | S f =>
    match code with
    | [] => hd 0 stack
    | IPush n :: c => run f c (n :: stack) env
    | ILoad i :: c => run f c (lookup env i :: stack) env
    | IAdd :: c => run f c (binop (fun a b => (a + b) mod m_val) stack) env
    | IMul :: c => run f c (binop (fun a b => (a * b) mod m_val) stack) env
    | IBind :: c => run f c (tl stack) (hd 0 stack :: env)
    | IUnbind :: c => run f c stack (tl env)
    end
  end.

Fixpoint gen (depth s : nat) : expr :=
  match depth with
  | 0 => if s mod 3 =? 0 then Var (s mod 4) else Num (s mod 7)
  | S d =>
    let s' := next s in
    match s mod 5 with
    | 0 => Add (gen d s') (gen d (next s'))
    | 1 => Mul (gen d s') (Num 1)
    | 2 => Let (gen d s') (gen d (next s'))
    | 3 => If0 (gen d s') (gen d (next s')) (Num 0)
    | _ => Add (Num 0) (gen d s')
    end
  end.


Definition round (depth i : nat) : nat :=
  let e := gen depth (i + 3) in
  let e' := simplify e in
  eval [1; 2; 3; 4] e + eval [1; 2; 3; 4] e' + run fuel_big (compile e' []) [] [1; 2; 3; 4].

Definition interp (depth rounds : nat) : nat :=
  fold_left (fun acc i => acc + round depth i) (seq 0 rounds) 0.

End GbInterp.

#[global] Instance m_lcg_mapping : OperationMapping (Ref (@GbInterp.m_lcg)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(65537)")).
#[global] Instance m_sum_mapping : OperationMapping (Ref (@GbInterp.m_sum)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(65535)")).
#[global] Instance m_clo_mapping : OperationMapping (Ref (@GbInterp.m_clo)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(4093)")).
#[global] Instance m_val_mapping : OperationMapping (Ref (@GbInterp.m_val)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(4096)")).
#[global] Instance m_key_mapping : OperationMapping (Ref (@GbInterp.m_key)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(4000)")).
#[global] Instance m_map_mapping : OperationMapping (Ref (@GbInterp.m_map)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(1000)")).
#[global] Instance fuel_big_mapping : OperationMapping (Ref (@GbInterp.fuel_big)) :=
  pure_cpp [] []
    (Structured (Verbatim "UINT64_C(100000000)")).
Set Crane Loopify.
Crane Extraction "gb_interp" GbInterp.
