#include "loopify_option.h"

/// lookup_opt key l looks up key in an association list.
std::optional<uint64_t> LoopifyOption::lookup_opt(
    uint64_t key, const LoopifyOption::list<std::pair<uint64_t, uint64_t>> &l) {
  const LoopifyOption::list<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyOption::list<std::pair<uint64_t, uint64_t>>::Nil>(
            _loop_l->v())) {
      return std::optional<uint64_t>();
    } else {
      const auto &[a0, a1] = std::get<
          typename LoopifyOption::list<std::pair<uint64_t, uint64_t>>::Cons>(
          _loop_l->v());
      if (a0.first == key) {
        return std::make_optional<uint64_t>(a0.second);
      } else {
        _loop_l = a1.get();
      }
    }
  }
}
