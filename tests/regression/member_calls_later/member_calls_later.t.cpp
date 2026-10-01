#include "member_calls_later.h"
#include <cassert>
#include <cstdio>

int main() {
  // [deeper] is hoisted onto [tree] and its body names [Helper::pick], a
  // module emitted after the struct.
  assert(std::holds_alternative<Nat::O>(Tree::leaf().deeper().v()));
  assert(std::holds_alternative<Nat::S>(
      Tree::node(Tree::leaf(), Tree::leaf()).deeper().v()));

  printf("All member_calls_later tests passed!\n");
  return 0;
}
