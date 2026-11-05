#include "boxed_element_concept.h"

/// A module type naming a mapped container of an element that recurses
/// through it, under a Boxed Element wrapper: the module's struct holds
/// crane::list<crane::box<rose>>, so the concept the module type becomes
/// has to ask for that type too, the element hole decided as everywhere
/// else, or the module satisfying the module type does not satisfy the
/// concept: children's result is asked for by std::same_as.
uint64_t BoxedElementConcept::size(const BoxedElementConcept::rose &r) {
  const auto &[n, kids] =
      std::get<typename BoxedElementConcept::rose::Node>(r.v());
  return ([&]() {
    auto go_impl =
        [](auto &_self_go,
           const crane::list<crane::box<BoxedElementConcept::rose>> &l)
        -> uint64_t {
      if (l.empty()) {
        return UINT64_C(0);
      } else {
        const BoxedElementConcept::rose &k = l.front();
        auto t = l.tail();
        return (size(k) + _self_go(_self_go, t));
      }
    };
    auto go = [&](const crane::list<crane::box<BoxedElementConcept::rose>> &l)
        -> uint64_t { return go_impl(go_impl, l); };
    return go(kids);
  }() + 1);
}

uint64_t BoxedElementConcept::Forest::count(
    const crane::list<crane::box<BoxedElementConcept::rose>> &l) {
  return List::template fold_left<uint64_t, BoxedElementConcept::rose>(
      [](uint64_t n, const BoxedElementConcept::rose &r) {
        return (n + size(r));
      },
      l, UINT64_C(0));
}

crane::list<crane::box<BoxedElementConcept::rose>>
BoxedElementConcept::Forest::children(const BoxedElementConcept::rose &r) {
  const auto &[n, kids] =
      std::get<typename BoxedElementConcept::rose::Node>(r.v());
  return kids;
}
