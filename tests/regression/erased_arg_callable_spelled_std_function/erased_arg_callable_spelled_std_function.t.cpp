#include <erased_arg_callable_spelled_std_function.h>

#include <cassert>

namespace {

List<Nat> nat_list(std::initializer_list<int> xs) {
  List<Nat> l = List<Nat>::nil();
  for (auto it = std::rbegin(xs); it != std::rend(xs); ++it) {
    Nat n = Nat::o();
    for (int i = 0; i < *it; ++i) {
      n = Nat::s(std::move(n));
    }
    l = List<Nat>::cons(std::move(n), std::move(l));
  }
  return l;
}

} // namespace

int main() {
  // The gate is that the call site below compiles at all: it passes a lambda
  // where template argument deduction runs against the callable parameter.
  assert(allsmall(nat_list({0, 4, 9})));
  assert(!allsmall(nat_list({0, 10})));
  assert(allsmall(List<Nat>::nil()));
  return 0;
}
