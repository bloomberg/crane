// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <inductive_letin_params.h>

#include <iostream>
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

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

template <typename T> static std::vector<T> to_vector(const List<T> &l) {
  std::vector<T> out;
  const List<T> *cur = &l;
  while (const auto *c = std::get_if<typename List<T>::Cons>(&cur->v())) {
    out.push_back(c->a);
    cur = c->l.get();
  }
  return out;
}

int main() {
  using M = InductiveLetinParams;

  // The fields after the let-in parameter keep their own type variables:
  // the second field is the [bool], the third the [list nat].
  ASSERT(M::sample.tri_first() == 7u);
  ASSERT(M::sample.tri_second() == true);
  ASSERT(to_vector(M::sample.tri_rest()) == (std::vector<uint64_t>{1, 2, 3}));
  ASSERT(M::sample_sum == 13u);

  ASSERT(to_vector(M::sample_tagged.tagged_firsts()) ==
         (std::vector<uint64_t>{1, 2}));
  ASSERT(to_vector(M::sample_tagged.tagged_seconds()) ==
         (std::vector<bool>{true, false}));

  // The index-bound field keeps the index's type variable.
  ASSERT(M::unwrapped == 5u);

  if (testStatus == 0) {
    std::cout << "All inductive_letin_params tests passed!" << std::endl;
  }
  return testStatus;
}
