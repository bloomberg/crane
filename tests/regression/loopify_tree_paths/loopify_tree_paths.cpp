#include <loopify_tree_paths.h>

#include <algorithm>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyTreePaths::map_cons(
    const unsigned int x,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> *_write = &_head;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_ll = ll;
  while (true) {
    if (std::holds_alternative<
            typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
            _loop_ll->v())) {
      *_write = List<std::shared_ptr<List<unsigned int>>>::nil();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
              _loop_ll->v());
      auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
          List<unsigned int>::cons(x, d_a0), nullptr);
      *_write = _cell;
      _write =
          &std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
               _cell->v_mut())
               .d_a1;
      _loop_ll = d_a1;
      continue;
    }
  }
  return _head;
}
