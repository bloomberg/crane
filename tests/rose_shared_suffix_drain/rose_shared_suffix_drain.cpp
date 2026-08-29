#include "rose_shared_suffix_drain.h"

uint64_t RoseSharedSuffixDrain::rsum(const RoseSharedSuffixDrain::rose &t) {
  const auto &[a0, a1] =
      std::get<typename RoseSharedSuffixDrain::rose::Node>(t.v());
  return (a0 + [&]() {
    auto go_impl = [](auto &_self_go,
                      const List<RoseSharedSuffixDrain::rose> &l) -> uint64_t {
      if (std::holds_alternative<
              typename List<RoseSharedSuffixDrain::rose>::Nil>(l.v())) {
        return UINT64_C(0);
      } else {
        const auto &[a2, a3] =
            std::get<typename List<RoseSharedSuffixDrain::rose>::Cons>(l.v());
        return (rsum(a2) + _self_go(_self_go, *a3));
      }
    };
    auto go = [&](const List<RoseSharedSuffixDrain::rose> &l) -> uint64_t {
      return go_impl(go_impl, l);
    };
    return go(*a1);
  }());
}

uint64_t RoseSharedSuffixDrain::run(uint64_t n) {
  List<RoseSharedSuffixDrain::rose> t = List<RoseSharedSuffixDrain::rose>::cons(
      rose::node(n, List<RoseSharedSuffixDrain::rose>::nil()),
      List<RoseSharedSuffixDrain::rose>::cons(
          rose::node((n + 1), List<RoseSharedSuffixDrain::rose>::nil()),
          List<RoseSharedSuffixDrain::rose>::cons(
              rose::node(((n + 1) + 1),
                         List<RoseSharedSuffixDrain::rose>::nil()),
              List<RoseSharedSuffixDrain::rose>::nil())));
  uint64_t a = rsum(rose::node(UINT64_C(1), t));
  uint64_t b = rsum(rose::node(UINT64_C(2), std::move(t)));
  return (a + b);
}
