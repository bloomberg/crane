#include <closure_map_escape.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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
__attribute__((pure))
ClosureMapEscape::mylist<std::function<unsigned int(unsigned int)>>
ClosureMapEscape::map_to_adders(
    const ClosureMapEscape::mylist<unsigned int> &l) {
  if (std::holds_alternative<
          typename ClosureMapEscape::mylist<unsigned int>::Mynil>(l.v())) {
    return mylist<std::function<unsigned int(unsigned int)>>::mynil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename ClosureMapEscape::mylist<unsigned int>::Mycons>(
            l.v());
    ClosureMapEscape::mylist<unsigned int> d_a1_value =
        clone_as_value<mylist<unsigned int>>(d_a1);
    auto add = std::make_shared<std::function<unsigned int(unsigned int)>>();
    *add = [=](unsigned int x) mutable -> unsigned int {
      if (x <= 0) {
        return d_a0;
      } else {
        unsigned int x_ = x - 1;
        return ((*add)(x_) + 1);
      }
    };
    return mylist<std::function<unsigned int(unsigned int)>>::mycons(
        (*add), map_to_adders(d_a1_value));
  }
}

__attribute__((pure)) unsigned int ClosureMapEscape::apply_first(
    const ClosureMapEscape::mylist<std::function<unsigned int(unsigned int)>>
        &fns,
    const unsigned int &arg) {
  if (std::holds_alternative<typename ClosureMapEscape::mylist<
          std::function<unsigned int(unsigned int)>>::Mynil>(fns.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] = std::get<typename ClosureMapEscape::mylist<
        std::function<unsigned int(unsigned int)>>::Mycons>(fns.v());
    return d_a0(arg);
  }
}

__attribute__((pure)) unsigned int ClosureMapEscape::sum_apply(
    const ClosureMapEscape::mylist<std::function<unsigned int(unsigned int)>>
        &fns,
    const unsigned int &arg) {
  if (std::holds_alternative<typename ClosureMapEscape::mylist<
          std::function<unsigned int(unsigned int)>>::Mynil>(fns.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] = std::get<typename ClosureMapEscape::mylist<
        std::function<unsigned int(unsigned int)>>::Mycons>(fns.v());
    return (d_a0(arg) + sum_apply(*(d_a1), arg));
  }
}
