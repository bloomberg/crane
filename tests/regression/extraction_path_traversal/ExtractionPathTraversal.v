(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Security regression: a Crane extraction target filename must stay within the
   configured output directory. Absolute paths and parent-directory ('..')
   traversal are rejected before any file is written (CWE-22 / CWE-73). The
   substantive assertions run while ExtractionPathTraversal.vo is built. *)
Require Crane.Extraction.

Definition ok : bool := true.

(* Absolute paths are rejected. *)
Fail Crane Extraction "/tmp/crane_escape" ok.

(* Parent-directory traversal is rejected, whether leading or hidden mid-path. *)
Fail Crane Extraction ".." ok.
Fail Crane Extraction "../crane_escape" ok.
Fail Crane Extraction "sub/../../crane_escape" ok.

(* The same guard protects the TestCompile variant, which shares the code path
   that derives output paths from the target filename. *)
Fail Crane Extraction TestCompile "../crane_escape" ok.
