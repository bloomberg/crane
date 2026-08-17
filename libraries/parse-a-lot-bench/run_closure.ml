(* SPDX-License-Identifier: BSD-3-Clause *)
let show name l =
  let n = List.length l in
  let ok = List.length (List.filter (fun b -> b) l) in
  Printf.printf "%-8s %d/%d rules closed%s\n" name ok n
    (if ok = n then "" else "   <-- FALLBACK WOULD FIRE");
  List.iteri (fun i b -> if not b then Printf.printf "    rule %d: NOT closed\n" i) l
let () =
  show "json"   ClosureCheck.chk_json;
  show "newick" ClosureCheck.chk_newick;
  show "ppm"    ClosureCheck.chk_ppm;
  show "xml"    ClosureCheck.chk_xml
