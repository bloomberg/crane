#include <loopify_predicates.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
LoopifyPredicates::remove_all(const unsigned int x,
                              const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_x = x;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              if (_loop_x == _args.d_a0) {
                std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                unsigned int _next_x = std::move(_loop_x);
                _loop_l = std::move(_next_l);
                _loop_x = std::move(_next_x);
              } else {
                auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                unsigned int _next_x = std::move(_loop_x);
                _loop_l = std::move(_next_l);
                _loop_x = std::move(_next_x);
              }
            }},
        _loop_l->v());
  }
  return _head;
}
