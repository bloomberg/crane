#include "boxed_element_block_template.h"

/// A Boxed Element container whose constructors are %result blocks.
///
/// A block's text is spliced as statements, and its %elem hole is decided
/// like a constructor template's: boxed where the element recurses through
/// the container, so list rose builds crane::list<crane::box<rose>>
/// while list nat builds crane::list<uint64_t>.
uint64_t
BoxedElementBlockTemplate::total(const BoxedElementBlockTemplate::rose &r) {
  const auto &[n0, kids] =
      std::get<typename BoxedElementBlockTemplate::rose::Node>(r.v());
  return (n0 + [&]() {
    auto go_impl =
        [](auto &_self_go,
           const crane::list<crane::box<BoxedElementBlockTemplate::rose>> &l)
        -> uint64_t {
      if (l.empty()) {
        return UINT64_C(0);
      } else {
        const BoxedElementBlockTemplate::rose &k = l.front();
        auto t = l.tail();
        return (total(k) + _self_go(_self_go, t));
      }
    };
    auto go =
        [&](const crane::list<crane::box<BoxedElementBlockTemplate::rose>> &l)
        -> uint64_t { return go_impl(go_impl, l); };
    return go(kids);
  }());
}

crane::list<uint64_t>
BoxedElementBlockTemplate::leaves(const BoxedElementBlockTemplate::rose &r) {
  const auto &[n0, kids] =
      std::get<typename BoxedElementBlockTemplate::rose::Node>(r.v());
  return [&]() -> crane::list<uint64_t> {
    crane::list<uint64_t> _r;
    _r = crane::cons(
        n0, ListDef::template map<BoxedElementBlockTemplate::rose, uint64_t>(
                [](const BoxedElementBlockTemplate::rose &k) {
                  const auto &[n1, kids0] =
                      std::get<typename BoxedElementBlockTemplate::rose::Node>(
                          k.v());
                  return n1;
                },
                kids));
    return _r;
  }();
}
