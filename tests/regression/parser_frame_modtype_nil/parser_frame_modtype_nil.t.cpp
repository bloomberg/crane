#include <parser_frame_modtype_nil.h>
#include <cassert>
#include <iostream>

// Regression test for the abstract-module-type nil-erasure bug: TheParser::parse
// let-binds `sk0 = (Fr [] tt [x], [])` where the outer `[]` is a `list frame`
// nil seen ABSTRACTLY (through module type `T`). Crane previously collapsed it to
// std::deque<crane::obj>{} instead of std::deque<typename D::Defs::frame>{}, so the
// template body failed to compile:
//   no viable conversion from 'pair<frame, deque<any>>'
//                          to 'pair<frame, deque<frame>>'
// Instantiating TheParser::parse forces the template body to compile; the fix
// preserves the concrete element type, so this now both compiles and runs.
//
// parse(x) = step_stack((Fr [] tt [x], []))
//          = length [x] + tail_lengths []
//          = 1 + 0 = 1.
int main() {
  auto n = TheParser::parse(Concrete_symbol::SA);
  std::cout << n << std::endl;
  assert(n == 1);
  return 0;
}
