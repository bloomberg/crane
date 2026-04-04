open Types

let categories = ["basics"; "monadic"; "regression"; "wip"]

let has_test_file dir =
  try
    let entries = Sys.readdir dir in
    Array.exists (fun f -> Filename.check_suffix f ".t.cpp") entries
  with Sys_error _ -> false

let find_tests_in_category root category =
  let category_path = Filename.concat root (Filename.concat "tests" category) in
  if not (Sys.file_exists category_path && Sys.is_directory category_path) then
    []
  else
    let entries = Sys.readdir category_path in
    let tests =
      Array.fold_left
        (fun acc name ->
          let full_path = Filename.concat category_path name in
          if Sys.is_directory full_path && has_test_file full_path then
            {category; name} :: acc
          else
            acc )
        []
        entries
    in
    List.sort compare_test_id tests

let find_all_tests root =
  let all_tests = List.concat_map (find_tests_in_category root) categories in
  List.sort compare_test_id all_tests

let find_changed_tests root =
  let run cmd =
    try
      let ic =
        Unix.open_process_in (Printf.sprintf "cd %s && %s" (Filename.quote root) cmd)
      in
      let lines = ref [] in
      ( try
          while true do
            lines := input_line ic :: !lines
          done
        with End_of_file -> () );
      ignore (Unix.close_process_in ic);
      !lines
    with _ -> []
  in
  let all_lines =
    run "git diff --name-only"
    @ run "git diff --name-only --cached"
    @ run "git ls-files --others --exclude-standard"
  in
  let parse_test_path line =
    let prefix = "tests/" in
    if String.length line > String.length prefix
       && String.sub line 0 (String.length prefix) = prefix
    then
      let rest = String.sub line (String.length prefix) (String.length line - String.length prefix) in
      match String.index_opt rest '/' with
      | Some i ->
        let category = String.sub rest 0 i in
        let after = String.sub rest (i + 1) (String.length rest - i - 1) in
        ( match String.index_opt after '/' with
        | Some j ->
          let name = String.sub after 0 j in
          Some { category; name }
        | None -> None )
      | None -> None
    else
      None
  in
  let seen = Hashtbl.create 32 in
  List.iter
    (fun line ->
      match parse_test_path line with
      | Some tid ->
        let key = tid.category ^ "/" ^ tid.name in
        if not (Hashtbl.mem seen key) then Hashtbl.replace seen key tid
      | None -> ())
    all_lines;
  Hashtbl.fold (fun _ v acc -> v :: acc) seen [] |> List.sort compare_test_id
