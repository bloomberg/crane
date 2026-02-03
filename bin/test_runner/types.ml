type test_id = {
  category : string;
  name : string;
}

type test_result = {
  test : test_id;
  passed : bool;
  output : string;
  duration : float;
}

type config = {
  jobs : int;
  verbose : bool;
  project_root : string;
}

let compare_test_id a b =
  let c = String.compare a.category b.category in
  if c <> 0 then c else String.compare a.name b.name

let test_to_dune_target t =
  Printf.sprintf "@tests/%s/%s/runtest" t.category t.name
