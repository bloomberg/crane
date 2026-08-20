#include "rose_shared_suffix_drain_size.h"

/// Same underlying defect as rose_shared_suffix_drain, reached with a
/// different consumer and three successive sharers of the same spine: the
/// generated ~rose() drains the list rose child cell by cell, checking
/// ownership only on the head shared_ptr, so the shared tail cells are
/// left moved-from for the next reader.
uint64_t
RoseSharedSuffixDrainSize::rsize(const RoseSharedSuffixDrainSize::rose &t) {
  const auto &[a0, a1] =
      std::get<typename RoseSharedSuffixDrainSize::rose::Node>(t.v());
  return ([&]() {
    auto go_impl =
        [](auto &_self_go,
           const List<RoseSharedSuffixDrainSize::rose> &l) -> uint64_t {
      if (std::holds_alternative<
              typename List<RoseSharedSuffixDrainSize::rose>::Nil>(l.v())) {
        return UINT64_C(0);
      } else {
        const auto &[a2, a3] =
            std::get<typename List<RoseSharedSuffixDrainSize::rose>::Cons>(
                l.v());
        return (rsize(a2) + _self_go(_self_go, *a3));
      }
    };
    auto go = [&](const List<RoseSharedSuffixDrainSize::rose> &l) -> uint64_t {
      return go_impl(go_impl, l);
    };
    return go(*a1);
  }() + 1);
}

uint64_t RoseSharedSuffixDrainSize::run(uint64_t n) {
  List<RoseSharedSuffixDrainSize::rose> t =
      List<RoseSharedSuffixDrainSize::rose>::cons(
          rose::node(n, List<RoseSharedSuffixDrainSize::rose>::nil()),
          List<RoseSharedSuffixDrainSize::rose>::cons(
              rose::node((n + 1), List<RoseSharedSuffixDrainSize::rose>::nil()),
              List<RoseSharedSuffixDrainSize::rose>::cons(
                  rose::node(((n + 1) + 1),
                             List<RoseSharedSuffixDrainSize::rose>::nil()),
                  List<RoseSharedSuffixDrainSize::rose>::cons(
                      rose::node(n,
                                 List<RoseSharedSuffixDrainSize::rose>::nil()),
                      List<RoseSharedSuffixDrainSize::rose>::nil()))));
  uint64_t a = rsize(rose::node(UINT64_C(1), t));
  uint64_t b = rsize(rose::node(UINT64_C(2), t));
  uint64_t c = rsize(rose::node(UINT64_C(3), std::move(t)));
  return ((a + b) + c);
}
