#include <list_closure_escape.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// BUG: partial applications stored in a custom list via FCons.
/// Each lambda for (sum_values t_i) captures t_i by &.
/// When build_fns returns, t1 and t2 are destroyed.
__attribute__((pure)) ListClosureEscape::fn_list
ListClosureEscape::build_fns(ListClosureEscape::tree t1,
                             ListClosureEscape::tree t2) {
  return fn_list::fcons(
      [=](unsigned int _x0) mutable -> unsigned int {
        return t1.sum_values(_x0);
      },
      fn_list::fcons([=](unsigned int _x0) mutable
                         -> unsigned int { return t2.sum_values(_x0); },
                     fn_list::fnil()));
}
