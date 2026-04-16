#include <loopify_predicates.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

std::shared_ptr<List<unsigned int>>
LoopifyPredicates::remove_all(const unsigned int x,
                              const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> *_write = &_head;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = List<unsigned int>::nil();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (x == d_a0) {
        _loop_l = d_a1;
        continue;
      } else {
        auto _cell = List<unsigned int>::cons(d_a0, nullptr);
        *_write = _cell;
        _write =
            &std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1;
        _loop_l = d_a1;
        continue;
      }
    }
  }
  return _head;
}
