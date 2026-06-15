(** Core types shared across all test runner modules.

    A test is identified by its [category] (subdirectory under [tests/]:
    ["basics"], ["monadic"], ["regression"], or ["wip"]) and its [name]
    (subdirectory within the category, e.g. ["list"] or ["stm_hash_map"]).

    The naming convention ties directory layout to build artifacts:
    - Source:     [tests/<category>/<name>/<Name>.v]
    - Test file:  [tests/<category>/<name>/<name>.t.cpp]
    - Executable: [_build/default/tests/<category>/<name>/<name>.t.exe] *)

(** Identifies a single test by its category and name. *)
type test_id = {
  category : string;
  name : string;
}

(** The outcome of running a single test. [duration] is wall-clock seconds
    for the executable only (excludes compilation). *)
type test_result = {
  test : test_id;
  passed : bool;
  output : string;
  duration : float;
}

(** Runner configuration, populated from command-line arguments.

    - [jobs]: number of parallel worker processes for Phase 2 (default: CPU count)
    - [verbose]: if true, print full stderr/stdout for failed tests
    - [project_root]: absolute path to the repository root (assumed to be cwd)
    - [folder]: when [Some cat], restrict to tests under [tests/<cat>/]
    - [changed_only]: when true, only run tests whose files differ from HEAD *)
type config = {
  jobs : int;
  verbose : bool;
  project_root : string;
  folder : string option;
  changed_only : bool;
}

(** Lexicographic ordering: category first, then name. *)
let compare_test_id a b =
  let c = String.compare a.category b.category in
  if c <> 0 then c else String.compare a.name b.name

(** Dune alias target for building and running a single test.
    Example: ["@tests/basics/list/runtest"]. *)
let test_to_dune_target t =
  Printf.sprintf "@tests/%s/%s/runtest" t.category t.name
