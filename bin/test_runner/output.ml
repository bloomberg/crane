open Types

let is_tty = Unix.isatty Unix.stdout

let red = if is_tty then "\027[0;31m" else ""
let green = if is_tty then "\027[0;32m" else ""
let yellow = if is_tty then "\027[0;33m" else ""
let cyan = if is_tty then "\027[0;36m" else ""
let bold = if is_tty then "\027[1m" else ""
let reset = if is_tty then "\027[0m" else ""

let separator = String.concat "" (List.init 59 (fun _ -> "\xE2\x94\x81"))

let print_header () =
  print_newline ();
  Printf.printf "%sRunning Crane Tests%s\n" bold reset;
  print_endline separator;
  print_newline ()

let print_result result =
  let status = if result.passed then
    Printf.sprintf "%s\xE2\x9C\x93 pass%s" green reset
  else
    Printf.sprintf "%s\xE2\x9C\x97 fail%s" red reset
  in
  Printf.printf "  %-25s %s\n" result.test.name status

let print_category_results category results =
  Printf.printf "%s%s/%s\n" cyan category reset;
  List.iter print_result results

let print_results results =
  let by_category = Hashtbl.create 4 in
  List.iter (fun r ->
    let cat = r.test.category in
    let existing = try Hashtbl.find by_category cat with Not_found -> [] in
    Hashtbl.replace by_category cat (r :: existing)
  ) results;

  let categories = ["basics"; "monadic"; "regression"; "wip"] in
  let first = ref true in
  List.iter (fun cat ->
    match Hashtbl.find_opt by_category cat with
    | None -> ()
    | Some tests ->
      if not !first then print_newline ();
      first := false;
      let sorted = List.sort (fun a b -> compare_test_id a.test b.test) tests in
      print_category_results cat sorted
  ) categories

let print_summary results =
  let total = List.length results in
  let passed = List.length (List.filter (fun r -> r.passed) results) in
  let failed = total - passed in
  print_newline ();
  print_endline separator;
  if failed = 0 then
    Printf.printf "%s%sAll %d tests passed%s\n" bold green total reset
  else
    Printf.printf "%sResults: %s%d passed%s, %s%d failed%s, %d total\n"
      bold green passed reset red failed reset total;
  print_newline ()

let print_verbose_errors results verbose_lines =
  let failed = List.filter (fun r -> not r.passed) results in
  if failed <> [] then begin
    Printf.printf "%s%sFailed test details:%s\n" bold red reset;
    print_endline separator;
    List.iter (fun r ->
      print_newline ();
      Printf.printf "%s[%s/%s]%s\n" yellow r.test.category r.test.name reset;
      let lines = String.split_on_char '\n' r.output in
      let shown_lines =
        if List.length lines <= verbose_lines then lines
        else
          let rec take n lst = match n, lst with
            | 0, _ | _, [] -> []
            | n, x :: xs -> x :: take (n - 1) xs
          in
          take verbose_lines lines
      in
      List.iter print_endline shown_lines;
      let total_lines = List.length lines in
      if total_lines > verbose_lines then
        Printf.printf "... (%d more lines)\n" (total_lines - verbose_lines)
    ) failed
  end
