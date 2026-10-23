#include "boxed_element_rose_tree.h"

/// A rose tree whose children are a mapped container with a Boxed
/// Element wrapper, as ParseALot maps lists: the element is boxed exactly
/// where it recurses through the container, so list rose is
/// crane::list<crane::box<rose>> while list nat stays unboxed.
uint64_t BoxedElementRoseTree::size(const BoxedElementRoseTree::rose &r) {
  const auto &[n, kids] =
      std::get<typename BoxedElementRoseTree::rose::Node>(r.v());
  return ([&]() {
    auto go_impl =
        [](auto &_self_go,
           const crane::list<crane::box<BoxedElementRoseTree::rose>> &l)
        -> uint64_t {
      if (l.empty()) {
        return UINT64_C(0);
      } else {
        const BoxedElementRoseTree::rose &k = l.front();
        auto t = l.tail();
        return (size(k) + _self_go(_self_go, t));
      }
    };
    auto go = [&](const crane::list<crane::box<BoxedElementRoseTree::rose>> &l)
        -> uint64_t { return go_impl(go_impl, l); };
    return go(kids);
  }() + 1);
}

uint64_t BoxedElementRoseTree::total(const BoxedElementRoseTree::rose &r) {
  const auto &[n0, kids] =
      std::get<typename BoxedElementRoseTree::rose::Node>(r.v());
  return (n0 + [&]() {
    auto go_impl =
        [](auto &_self_go,
           const crane::list<crane::box<BoxedElementRoseTree::rose>> &l)
        -> uint64_t {
      if (l.empty()) {
        return UINT64_C(0);
      } else {
        const BoxedElementRoseTree::rose &k = l.front();
        auto t = l.tail();
        return (total(k) + _self_go(_self_go, t));
      }
    };
    auto go = [&](const crane::list<crane::box<BoxedElementRoseTree::rose>> &l)
        -> uint64_t { return go_impl(go_impl, l); };
    return go(kids);
  }());
}

crane::list<uint64_t>
BoxedElementRoseTree::labels(const BoxedElementRoseTree::rose &r) {
  const auto &[n0, kids] =
      std::get<typename BoxedElementRoseTree::rose::Node>(r.v());
  return crane::cons(
      n0, ListDef::template map<BoxedElementRoseTree::rose, uint64_t>(
              [](const BoxedElementRoseTree::rose &k) {
                const auto &[n1, kids0] =
                    std::get<typename BoxedElementRoseTree::rose::Node>(k.v());
                return n1;
              },
              kids));
}
