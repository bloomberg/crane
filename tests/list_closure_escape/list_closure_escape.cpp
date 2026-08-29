#include "list_closure_escape.h"

ListClosureEscape::fn_list
ListClosureEscape::build_fns(ListClosureEscape::tree t1,
                             ListClosureEscape::tree t2) {
  return fn_list::fcons(
      [=](uint64_t _x0) mutable -> uint64_t { return t1.sum_values(_x0); },
      fn_list::fcons(
          [=](uint64_t _x0) mutable -> uint64_t { return t2.sum_values(_x0); },
          fn_list::fnil()));
}
