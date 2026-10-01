#include <generic_monad_result_rewrapped.h>

#include <cassert>
#include <vector>

namespace {

Nat nat_of(int k) {
  Nat n = Nat::o();
  for (int i = 0; i < k; ++i) {
    n = Nat::s(std::move(n));
  }
  return n;
}

int int_of(Nat n) {
  int k = 0;
  while (std::holds_alternative<typename Nat::S>(n.v())) {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    n = *a0;
    ++k;
  }
  return k;
}

std::vector<int> to_vector(List<Nat> l) {
  std::vector<int> v;
  while (std::holds_alternative<typename List<Nat>::Cons>(l.v())) {
    const auto &[hd, tl] = std::get<typename List<Nat>::Cons>(l.v());
    v.push_back(int_of(hd));
    l = *tl;
  }
  return v;
}

} // namespace

int main() {
  // The gate is that [run] compiles at all: its [ITree.bind] takes a
  // generic-monad call result, which is already a tree.
  List<Nat> l = List<Nat>::cons(
      nat_of(1), List<Nat>::cons(nat_of(2), List<Nat>::cons(nat_of(3),
                                                            List<Nat>::nil())));
  assert(to_vector(GenericMonadResultRewrapped::go(l)->run()) == (std::vector<int>{2, 4, 6}));
  assert(to_vector(GenericMonadResultRewrapped::go(List<Nat>::nil())->run()).empty());
  return 0;
}
