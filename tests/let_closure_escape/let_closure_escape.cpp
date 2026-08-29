#include "let_closure_escape.h"

LetClosureEscape::fn_box
LetClosureEscape::let_escape(LetClosureEscape::tree t) {
  std::function<uint64_t(uint64_t)> f = [=](uint64_t _x0) mutable -> uint64_t {
    return t.sum_values(_x0);
  };
  return fn_box::box(f);
}
