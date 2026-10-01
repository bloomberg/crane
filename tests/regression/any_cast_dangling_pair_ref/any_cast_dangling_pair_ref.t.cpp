// Two bugs when destructuring erased pairs:
//
// Bug A (swap_pair): match-destructuring generates
//   const crane::obj &b = any_cast<pair<any,any>>(t).first;
//   → temporary pair dies at semicolon, b dangles.
//   UB detectable with ASan (CRANE_CPP_SANITIZE=1).
//
// Bug B (use_both): "let tail := snd vs in fst tail" generates
//   auto tail = any_cast<pair<any,any>>(vs).second;
//   Ty::sym_semty b = std::move(tail).first;
//   → crane::obj has no .first; compile error.

#include "AnyCastDanglingPairRef.h"

#include <any>
#include <cassert>
#include <iostream>
#include <utility>

struct MySym {
  int id;
};

struct MyTypes {
  using sym = MySym;
  using sym_semty = crane::obj;
};

int main() {
  using D = AnyCastDanglingPairRef::Destruct<MyTypes>;

  crane::obj inner = std::make_pair(crane::obj(42), crane::obj(std::monostate{}));
  crane::obj vs = std::make_pair(crane::obj(10), inner);

  MySym x{0}, y{1};

  // Bug A: dangling reference — UB, needs ASan to catch
  auto r1 = D::swap_pair(x, y, {}, vs);
  (void)r1;

  // Bug B: was compile error (crane::obj has no .first), now fixed
  auto r2 = D::use_both(x, y, {}, vs);
  (void)r2;

  std::cout << "any_cast_dangling_pair_ref: passed" << std::endl;
  return 0;
}
