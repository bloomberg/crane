(* SPDX-License-Identifier: BSD-3-Clause *)
(* Fuzzes the interned DFA's closure certificate: builds random regexes over a
   two-letter alphabet and reports any whose state list is not closed (i.e.
   whose Brzozowski table fill ran out of fuel), plus the worst observed
   states-vs-fuel-bound ratio. *)
module R = Literal.LXR.Mem.STT.R.Defs.Regexes
open R

let rec nat2int = function Datatypes.O -> 0 | Datatypes.S n -> 1 + nat2int n

let rec len = function
  | EmptySet | EmptyStr | Char _ -> 1
  | App (a, b) | Union (a, b) -> 1 + len a + len b
  | Star a -> 1 + len a

let rec show = function
  | EmptySet -> "0" | EmptyStr -> "1"
  | Char c -> String.make 1 c
  | App (a, b) -> "(" ^ show a ^ show b ^ ")"
  | Union (a, b) -> "(" ^ show a ^ "|" ^ show b ^ ")"
  | Star a -> show a ^ "*"

let rec rnd d =
  if d = 0 then
    match Random.int 4 with
    | 0 -> Char 'a' | 1 -> Char 'b' | 2 -> EmptyStr | _ -> EmptySet
  else
    match Random.int 5 with
    | 0 -> Char (if Random.bool () then 'a' else 'b')
    | 1 -> Star (rnd (d - 1))
    | 2 | 3 -> App (rnd (d - 1), rnd (d - 1))
    | _ -> Union (rnd (d - 1), rnd (d - 1))

let () =
  let iters = try int_of_string Sys.argv.(1) with _ -> 2000 in
  let depth = try int_of_string Sys.argv.(2) with _ -> 4 in
  Random.self_init ();
  let bad = ref 0 and worst = ref 0.0 and worste = ref "" in
  for _ = 1 to iters do
    let e = rnd (1 + Random.int depth) in
    let ok = ClosureCheck.chk1 e in
    let n = nat2int (ClosureCheck.nstates1 e) and l = len e in
    if not ok then begin
      incr bad;
      Printf.printf "NOT CLOSED  len=%d states=%d  %s\n%!" l n (show e)
    end;
    let r = log (float_of_int (n + 1)) /. log 2. /. float_of_int (l + 1) in
    if r > !worst then (worst := r; worste := Printf.sprintf "%s (len %d, %d states)" (show e) l n)
  done;
  Printf.printf "%d regexes: %d not closed\n" iters !bad;
  Printf.printf "worst log2(states+1)/(len+1) = %.3f  %s\n" !worst !worste
