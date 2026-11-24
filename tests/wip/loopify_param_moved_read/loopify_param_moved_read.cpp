#include "loopify_param_moved_read.h"

Sum<List<uint64_t>, String>
LoopifyParamMovedRead::g(const LoopifyParamMovedRead::tree &t, String s) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const LoopifyParamMovedRead::tree *_loop_t = &t;
  while (true) {
    if (std::holds_alternative<typename LoopifyParamMovedRead::tree::Leaf>(
            _loop_t->v())) {
      if (std::holds_alternative<typename LoopifyParamMovedRead::tree::Leaf>(
              _loop_t->v())) {
        return Sum<List<uint64_t>, String>::inr(
            List<bool>::nil().template fold_left<String>(
                [=, s = std::move(s)](String, bool) { return s; },
                String::emptystring()));
      } else {
        List<uint64_t> l = List<uint64_t>::nil();
        Sum<List<uint64_t>, String> acc =
            Sum<List<uint64_t>, String>::inr(std::move(s));
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
          return Sum<List<uint64_t>, String>::inr(String::emptystring());
        } else {
          return acc;
        }
      }
    } else {
      const auto &[_, _, r0] =
          std::get<typename LoopifyParamMovedRead::tree::Node>(_loop_t->v());
      _loop_t = crane_raw(r0);
    }
  }
}
