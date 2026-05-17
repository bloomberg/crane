#include "closure_map_escape.h"

/// Build a list of closures from a list of nats using LOCAL FIXPOINTS.
/// Each recursive call creates a fixpoint add that captures the
/// pattern variable h from the match.
///
/// BUG: Each local fixpoint uses & capture. The pattern variable h
/// is a local binding within the match IIFE. The fixpoint is stored in
/// mycons (a constructor), so return_captures_by_value does NOT
/// apply. After the match, h goes out of scope, and the closure
/// references dangling memory.
///
/// Difference from fix_escape_match: uses a USER-DEFINED list type
/// (not stdlib option), and the fixpoints are built RECURSIVELY
/// from list elements (not a single fixpoint).
ClosureMapEscape::mylist<std::function<uint64_t(uint64_t)>>
ClosureMapEscape::map_to_adders(const ClosureMapEscape::mylist<uint64_t> &l) {
  if (std::holds_alternative<
          typename ClosureMapEscape::mylist<uint64_t>::Mynil>(l.v())) {
    return mylist<std::function<uint64_t(uint64_t)>>::mynil();
  } else {
    const auto &[a0, a1] =
        std::get<typename ClosureMapEscape::mylist<uint64_t>::Mycons>(l.v());
    const ClosureMapEscape::mylist<uint64_t> &a1_value = *a1;
    auto add_impl = [=](auto &_self_add, uint64_t x) mutable -> uint64_t {
      if (x <= 0) {
        return a0;
      } else {
        uint64_t x_ = x - 1;
        return (_self_add(_self_add, x_) + 1);
      }
    };
    auto add = [=](uint64_t x) mutable -> uint64_t {
      return add_impl(add_impl, x);
    };
    return mylist<std::function<uint64_t(uint64_t)>>::mycons(
        add, map_to_adders(a1_value));
  }
}

uint64_t ClosureMapEscape::apply_first(
    const ClosureMapEscape::mylist<std::function<uint64_t(uint64_t)>> &fns,
    uint64_t arg) {
  if (std::holds_alternative<typename ClosureMapEscape::mylist<
          std::function<uint64_t(uint64_t)>>::Mynil>(fns.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename ClosureMapEscape::mylist<
        std::function<uint64_t(uint64_t)>>::Mycons>(fns.v());
    return a0(arg);
  }
}

uint64_t ClosureMapEscape::sum_apply(
    const ClosureMapEscape::mylist<std::function<uint64_t(uint64_t)>> &fns,
    uint64_t arg) {
  if (std::holds_alternative<typename ClosureMapEscape::mylist<
          std::function<uint64_t(uint64_t)>>::Mynil>(fns.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename ClosureMapEscape::mylist<
        std::function<uint64_t(uint64_t)>>::Mycons>(fns.v());
    return (a0(arg) + sum_apply(*a1, arg));
  }
}
