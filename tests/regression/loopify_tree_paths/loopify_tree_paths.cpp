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
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_ll = ll;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
            _loop_ll->v())) {
      if (_last) {
        std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            _last->v_mut())
            .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
      } else {
        _head = List<std::shared_ptr<List<unsigned int>>>::nil();
      }
      _continue = false;
    } else {
      const auto &_m = *std::get_if<
          typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
          &_loop_ll->v());
      auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
          List<unsigned int>::cons(x, _m.d_a0), nullptr);
      if (_last) {
        std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            _last->v_mut())
            .d_a1 = _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      _loop_ll = _m.d_a1;
      continue;
    }
  }
  return _head;
}
