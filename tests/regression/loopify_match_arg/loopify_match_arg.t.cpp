// Minimal test for loopify bugs:
//   Bug 1: Missing #include <vector> (compile error)
//   Bug 2: Partial loopification produces mismatched std::visit
//          return types (compile error)
//
// If both bugs are fixed the generated code compiles and these
// runtime checks should pass.

#include <loopify_match_arg.h>

#include <cassert>
#include <iostream>

template <typename T>
static List<T> from_vec(const std::vector<T> &v) {
  List<T> xs = List<T>::nil();
  for (auto it = v.rbegin(); it != v.rend(); ++it) {
    xs = List<T>::cons(*it, std::move(xs));
  }
  return xs;
}

int main() {
  using Cell = LoopifyMatchArg::Cell;

  auto empty = from_vec<Cell>({});
  auto row = from_vec<Cell>({Cell::e_WALL, Cell::e_DOT, Cell::e_EMPTY,
                             Cell::e_DOT, Cell::e_DOT});

  // my_length
  std::cout << "length(empty) = " << LoopifyMatchArg::my_length(empty)
            << std::endl;
  assert(LoopifyMatchArg::my_length(empty) == 0);

  std::cout << "length(row)   = " << LoopifyMatchArg::my_length(row)
            << std::endl;
  assert(LoopifyMatchArg::my_length(row) == 5);

  // count_dots
  std::cout << "count_dots(empty) = " << LoopifyMatchArg::count_dots(empty)
            << std::endl;
  assert(LoopifyMatchArg::count_dots(empty) == 0);

  std::cout << "count_dots(row)   = " << LoopifyMatchArg::count_dots(row)
            << std::endl;
  assert(LoopifyMatchArg::count_dots(row) == 3);

  std::cout << "PASS" << std::endl;
  return 0;
}
