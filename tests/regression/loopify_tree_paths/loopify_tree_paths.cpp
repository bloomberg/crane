#include "loopify_tree_paths.h"

List<List<uint64_t>>
LoopifyTreePaths::map_cons(uint64_t x, const List<List<uint64_t>> &ll) {
  std::unique_ptr<List<List<uint64_t>>> _head{};
  std::unique_ptr<List<List<uint64_t>>> *_write = &_head;
  const List<List<uint64_t>> *_loop_ll = &ll;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_ll->v())) {
      *_write =
          std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_ll->v());
      auto _cell = std::make_unique<List<List<uint64_t>>>(
          typename List<List<uint64_t>>::Cons(List<uint64_t>::cons(x, a0),
                                              nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut()).a1;
      _loop_ll = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}
