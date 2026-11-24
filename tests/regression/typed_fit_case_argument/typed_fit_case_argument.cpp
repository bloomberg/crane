#include "typed_fit_case_argument.h"

uint64_t TypedFitCaseArgument::via_method(bool b) {
  return sz_tree::sz(
      (b ? tree::leaf() : tree::node(tree::leaf(), UINT64_C(0), tree::leaf())));
}

uint64_t TypedFitCaseArgument::via_local_fix(uint64_t n) {
  return [&]() {
    auto go =
        [](const List<bool> &l,
           List<crane::fn<uint64_t(uint64_t)>> acc)
             -> List<crane::fn<uint64_t(uint64_t)>> {
          // Loop replaces the tail recursion: each recursive call updates the
          // loop variables.
          const List<bool> *_loop_l = &l;
          while (true) {
            if (std::holds_alternative<typename List<bool>::Nil>(_loop_l->v())) {
              return acc;
            } else {
              const auto &[_, a1] =
                  std::get<typename List<bool>::Cons>(_loop_l->v());
              _loop_l = crane_raw(a1);
            }
          }
        };
    return go(
        [&]() -> List<bool> {
          if (n <= 0) {
            return List<bool>::nil();
          } else {
            uint64_t _x = n - 1;
            return List<bool>::cons(true, List<bool>::nil());
          }
        }(),
        List<crane::fn<uint64_t(uint64_t)>>::nil());
  }().length();
}

TypedFitCaseArgument::r3 TypedFitCaseArgument::via_record(const List<bool> &l) {
  return r3{UINT64_C(0),
            (std::holds_alternative<typename List<bool>::Nil>(l.v())
                 ? List<uint64_t>::nil()
                 : List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil())),
            true};
}

uint64_t TypedFitCaseArgument::via_record_len(const List<bool> &l) {
  return via_record(l).rb.length();
}

uint64_t TypedFitCaseArgument::plain_f(const TypedFitCaseArgument::tree &t) {
  if (std::holds_alternative<typename TypedFitCaseArgument::tree::Leaf>(t.v())) {
    return UINT64_C(1);
  } else {
    return UINT64_C(2);
  }
}

uint64_t TypedFitCaseArgument::plain(bool b) {
  return plain_f(
      (b ? tree::leaf() : tree::node(tree::leaf(), UINT64_C(0), tree::leaf())));
}
