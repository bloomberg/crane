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
ClosureMapEscape::mylist<std::function<unsigned int(unsigned int)>>
ClosureMapEscape::map_to_adders(
    const ClosureMapEscape::mylist<unsigned int> &l) {
  if (std::holds_alternative<
          typename ClosureMapEscape::mylist<unsigned int>::Mynil>(l.v())) {
    return mylist<std::function<unsigned int(unsigned int)>>::mynil();
  } else {
    const auto &[a0, a1] =
        std::get<typename ClosureMapEscape::mylist<unsigned int>::Mycons>(
            l.v());
    const ClosureMapEscape::mylist<unsigned int> &a1_value = *a1;
    auto add_impl = [=](auto &_self_add,
                        unsigned int x) mutable -> unsigned int {
      if (x <= 0) {
        return a0;
      } else {
        unsigned int x_ = x - 1;
        return (_self_add(_self_add, x_) + 1);
      }
    };
    auto add = [=](unsigned int x) mutable -> unsigned int {
      return add_impl(add_impl, x);
    };
    return mylist<std::function<unsigned int(unsigned int)>>::mycons(
        add, map_to_adders(a1_value));
  }
}

unsigned int ClosureMapEscape::apply_first(
    const ClosureMapEscape::mylist<std::function<unsigned int(unsigned int)>>
        &fns,
    unsigned int arg) {
  if (std::holds_alternative<typename ClosureMapEscape::mylist<
          std::function<unsigned int(unsigned int)>>::Mynil>(fns.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<typename ClosureMapEscape::mylist<
        std::function<unsigned int(unsigned int)>>::Mycons>(fns.v());
    return a0(arg);
  }
}

unsigned int ClosureMapEscape::sum_apply(
    const ClosureMapEscape::mylist<std::function<unsigned int(unsigned int)>>
        &fns,
    unsigned int arg) {
  if (std::holds_alternative<typename ClosureMapEscape::mylist<
          std::function<unsigned int(unsigned int)>>::Mynil>(fns.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<typename ClosureMapEscape::mylist<
        std::function<unsigned int(unsigned int)>>::Mycons>(fns.v());
    return (a0(arg) + sum_apply(*a1, arg));
  }
}
