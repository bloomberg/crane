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
    let tests = Array.fold_left (fun acc name ->
      let full_path = Filename.concat category_path name in
      if Sys.is_directory full_path && has_test_file full_path then
        { category; name } :: acc
      else
        acc
    ) [] entries in
    List.sort compare_test_id tests

let find_all_tests root =
  let all_tests = List.concat_map (find_tests_in_category root) categories in
  List.sort compare_test_id all_tests
