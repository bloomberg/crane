#include <reuse_self_cycle.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
ReuseSelfCycle::length(const std::shared_ptr<ReuseSelfCycle::mylist> &l) {
  if (std::holds_alternative<typename ReuseSelfCycle::mylist::Mycons>(l->v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename ReuseSelfCycle::mylist::Mycons>(l->v());
    return (1u + length(d_a1));
  } else {
    return 0u;
  }
}

/// BUG: The reuse optimization fires and sets d_a1 = l, where l
/// is the scrutinee (the very node being mutated).
/// This creates a CYCLE: the node's tail points to itself.
///
/// In Rocq, mycons x l creates a FRESH cons cell whose tail is l.
/// With reuse, the SAME cell is mutated: d_a1 <- l makes the cell
/// point to itself.
///
/// Calling length on the result causes infinite recursion -> stack overflow.
///
/// Reuse fires because:
/// 1. l escapes in else l -> owned
/// 2. mycons branch tail is mycons with arity 2 = 2
/// 3. mycons is index 0 -> List.hd picks it
/// 4. use_count() == 1 for fresh values
std::shared_ptr<ReuseSelfCycle::mylist>
ReuseSelfCycle::prepend_self(std::shared_ptr<ReuseSelfCycle::mylist> l,
                             const bool b) {
  if (b) {
    if (std::holds_alternative<typename ReuseSelfCycle::mylist::Mycons>(
            l->v())) {
      const auto &[d_a0, d_a1] =
          std::get<typename ReuseSelfCycle::mylist::Mycons>(l->v());
      return mylist::mycons(d_a0, l);
    } else {
      return mylist::mynil();
    }
  } else {
    return l;
  }
}
