#include "map_returns_closure.h"

/// Mapping a list to a list of {e closures}.  The element type of the
/// result is a function type, and the emitted List::map call fails its
/// std::is_invocable_r_v constraint because the generated lambda returns a
/// lambda rather than the declared element type.
List<std::function<uint64_t(uint64_t)>>
MapReturnsClosure::make_adders(const List<uint64_t> &xs) {
  return xs.template map<std::function<uint64_t(uint64_t)>>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); });
}

uint64_t
MapReturnsClosure::apply_all(const List<std::function<uint64_t(uint64_t)>> &fs,
                             uint64_t n) {
  return fs.template fold_left<uint64_t>(
      [=](uint64_t acc, std::function<uint64_t(uint64_t)> f) mutable {
        return (acc + f(n));
      },
      UINT64_C(0));
}
