#include "boxed_element_drain.h"

/// A rose tree over a container with a Boxed Element wrapper and a
/// Drain clause, as ParseALot's ConsList.v maps lists: the destructor
/// takes a deep tree apart through the drain rather than by recursion.
uint64_t BoxedElementDrain::total(const BoxedElementDrain::rose &r) {
  const auto &[n0, kids] =
      std::get<typename BoxedElementDrain::rose::Node>(r.v());
  return (n0 + [&]() {
    auto go_impl =
        [](auto &_self_go,
           const crane::list<BoxedElementDrain::rose> &l) -> uint64_t {
      if (l.empty()) {
        return UINT64_C(0);
      } else {
        const BoxedElementDrain::rose &k = l.front();
        auto t = l.tail();
        return (total(k) + _self_go(_self_go, t));
      }
    };
    auto go = [&](const crane::list<BoxedElementDrain::rose> &l) -> uint64_t {
      return go_impl(go_impl, l);
    };
    return go(kids);
  }());
}

BoxedElementDrain::rose BoxedElementDrain::spine(uint64_t d) {
  if (d <= 0) {
    return rose::node(UINT64_C(1), crane::list<BoxedElementDrain::rose>{});
  } else {
    uint64_t d_ = d - 1;
    return rose::node(
        UINT64_C(1),
        crane::cons(spine(d_), crane::list<BoxedElementDrain::rose>{}));
  }
}
