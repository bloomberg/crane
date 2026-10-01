#include <grammar_action_pairlist_crash.h>

#include <any>
#include <deque>
#include <functional>
#include <iostream>
#include <utility>
#include <variant>

// The extracted C++ JSON parser throws std::bad_any_cast on every array/object
// because the semantic ACTION converting an erased list leaf to a concrete-
// element list emits a redundant, WRONG middle cast:
//   crane_container_cast<deque<Concrete>>(
//       any_cast<deque<Concrete>>(          <-- applied to a deque<any> -> throws
//           any_cast<deque<any>>(prs)))
// Here we invoke entries[0]'s VAssoc action (the (Value,[NT Obj]) production,
// like JSON's Value->Obj / JAssoc) on an erased empty object list, exactly as
// the parser does, and observe the crash.
int main() {
  // entries[0] = (Value, [NT Obj]); .a1 = (predicate, action) pair (both boxed).
  const auto &prod_semty = entries[0].a1;         // std::pair<crane::obj, crane::obj>
  auto action = crane::any_cast<crane::fn<crane::obj(crane::obj)>>(prod_semty.second);

  // The erased Obj value at runtime: an empty list, represented as the
  // canonical fully-flat std::deque<crane::obj> (what the nil producer /
  // erased parser stack holds -- a bare crane::obj per element, not a
  // structure-preserving deque<pair<any,any>>).
  crane::obj prs = std::deque<crane::obj>{};
  // The action receives the RHS tuple (prs, tt) boxed as crane::obj.
  crane::obj tup =
      crane::obj(std::make_pair(prs, crane::obj(std::monostate{})));

  std::cout << "invoking VAssoc action on erased empty object list..." << std::endl;
  bool threw = false;
  try {
    crane::obj result = action(tup);   // -> Val::vassoc(crane_container_cast(any_cast<deque<pair<string,Val>>>(...)))
    std::cout << "action returned normally (bug fixed)" << std::endl;
  } catch (const std::bad_any_cast &e) {
    threw = true;
    std::cout << "bad_any_cast thrown by VAssoc action: " << e.what() << std::endl;
  }

  if (threw) {
    std::cout << "REPRODUCED: action-path redundant middle any_cast crashes."
              << std::endl;
    return 1;   // non-zero: the bug is present
  }
  std::cout << "OK: no crash." << std::endl;
  return 0;
}
