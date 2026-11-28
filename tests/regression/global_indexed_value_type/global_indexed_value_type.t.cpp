// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <global_indexed_value_type.h>

#include <iostream>
#include <type_traits>
#include <variant>
#include <vector>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

template <typename T> std::vector<T> to_vector(const List<T> &l) {
  std::vector<T> out;
  const List<T> *cur = &l;
  while (auto *c = std::get_if<typename List<T>::Cons>(&cur->v())) {
    out.push_back(c->a);
    cur = c->l.get();
  }
  return out;
}

using Lists = std::vector<std::vector<uint64_t>>;

Lists to_lists(const List<List<uint64_t>> &l) {
  Lists out;
  for (const auto &x : to_vector(l))
    out.push_back(to_vector(x));
  return out;
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  using M = GlobalIndexedValueType;

  // The value type at index 0 is a list of numbers, not crane::obj.
  static_assert(std::is_same_v<decltype(M::via_notation(0)),
                               List<List<uint64_t>>>);
  static_assert(std::is_same_v<decltype(M::number()), uint64_t>);

  ASSERT((to_lists(M::via_notation(3)) == Lists{{}, {1, 2}, {}}));
  ASSERT((to_lists(M::via_definition(3)) == Lists{{}, {3, 4}, {}}));
  ASSERT((to_lists(M::lists_concrete(2)) == Lists{{7}, {}}));
  ASSERT(M::number() == 9u);

  if (testStatus == 0) {
    std::cout << "All global_indexed_value_type tests passed!\n";
  }
  return testStatus;
}
