#include <loopify_structures.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// Nested and complex data structures.
/// Helper: sum all elements in a list of nested structures.
/// Handles both tree and list levels in one function for full loopification.
__attribute__((pure)) unsigned int LoopifyStructures::sum_nested_list_fuel(
    const unsigned int fuel,
    const std::shared_ptr<List<std::shared_ptr<LoopifyStructures::nested>>>
        &l) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyStructures::nested>>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyStructures::nested::Elem &>()
                 .d_a0) _s0;
  };

  struct _Call2 {
    decltype(std::declval<const typename LoopifyStructures::nested::NList &>()
                 .d_a0) _s0;
    unsigned int _s1;
  };

  struct _Call3 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<
                  List<std::shared_ptr<LoopifyStructures::nested>>>
                  l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = 0u;
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<
                            std::shared_ptr<LoopifyStructures::nested>>::Nil &)
                            -> void { _result = 0u; },
                        [&](const typename List<
                            std::shared_ptr<LoopifyStructures::nested>>::Cons
                                &_args) -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename LoopifyStructures::nested::
                                          Elem &_args0) -> void {
                                    _stack.push_back(_Call1{_args0.d_a0});
                                    _stack.push_back(_Enter{_args.d_a1, f});
                                  },
                                  [&](const typename LoopifyStructures::nested::
                                          NList &_args0) -> void {
                                    _stack.push_back(_Call2{_args0.d_a0, f});
                                    _stack.push_back(_Enter{_args.d_a1, f});
                                  }},
                              _args.d_a0->v());
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); },
            [&](_Call2 _f) {
              _stack.push_back(_Call3{_result});
              _stack.push_back(_Enter{_f._s0, _f._s1});
            },
            [&](_Call3 _f) { _result = (_result + _f._s0); }},
        _frame);
  }
  return _result;
}

/// Helper: compute max depth among a list of nested structures.
__attribute__((pure)) unsigned int LoopifyStructures::depth_nested_list_fuel(
    const unsigned int fuel,
    const std::shared_ptr<List<std::shared_ptr<LoopifyStructures::nested>>>
        &l) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyStructures::nested>>> l;
    const unsigned int fuel;
  };

  struct _Call1 {};

  struct _Call2 {
    const typename List<std::shared_ptr<LoopifyStructures::nested>>::Cons _s0;
    unsigned int _s1;
  };

  struct _Call3 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<
                  List<std::shared_ptr<LoopifyStructures::nested>>>
                  l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = 0u;
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<
                            std::shared_ptr<LoopifyStructures::nested>>::Nil &)
                            -> void { _result = 0u; },
                        [&](const typename List<
                            std::shared_ptr<LoopifyStructures::nested>>::Cons
                                &_args) -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename LoopifyStructures::nested::
                                          Elem &) -> void {
                                    _stack.push_back(_Call1{});
                                    _stack.push_back(_Enter{_args.d_a1, f});
                                  },
                                  [&](const typename LoopifyStructures::nested::
                                          NList &_args0) -> void {
                                    _stack.push_back(_Call2{_args, f});
                                    _stack.push_back(_Enter{_args0.d_a0, f});
                                  }},
                              _args.d_a0->v());
                        }},
                    l->v());
              }
            },
            [&](_Call1) {
              unsigned int rest_max = _result;
              if (0u <= rest_max) {
                _result = rest_max;
              } else {
                _result = 0u;
              }
            },
            [&](_Call2 _f) {
              const typename List<
                  std::shared_ptr<LoopifyStructures::nested>>::Cons _args =
                  _f._s0;
              unsigned int f = _f._s1;
              unsigned int d = (_result + 1);
              _stack.push_back(_Call3{d});
              _stack.push_back(_Enter{_args.d_a1, f});
            },
            [&](_Call3 _f) {
              unsigned int d = _f._s0;
              unsigned int rest_max = _result;
              if (d <= rest_max) {
                _result = rest_max;
              } else {
                _result = d;
              }
            }},
        _frame);
  }
  return _result;
}

/// Helper: flatten a list of nested structures to a flat list of nats.
std::shared_ptr<List<unsigned int>> LoopifyStructures::flatten_nested_list_fuel(
    const unsigned int fuel,
    const std::shared_ptr<List<std::shared_ptr<LoopifyStructures::nested>>>
        &l) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyStructures::nested>>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyStructures::nested::Elem &>()
                 .d_a0) _s0;
  };

  struct _Call2 {
    decltype(std::declval<const typename LoopifyStructures::nested::NList &>()
                 .d_a0) _s0;
    unsigned int _s1;
  };

  struct _Call3 {
    std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<
                  List<std::shared_ptr<LoopifyStructures::nested>>>
                  l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = List<unsigned int>::nil();
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<
                            std::shared_ptr<LoopifyStructures::nested>>::Nil &)
                            -> void { _result = List<unsigned int>::nil(); },
                        [&](const typename List<
                            std::shared_ptr<LoopifyStructures::nested>>::Cons
                                &_args) -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename LoopifyStructures::nested::
                                          Elem &_args0) -> void {
                                    _stack.push_back(_Call1{_args0.d_a0});
                                    _stack.push_back(_Enter{_args.d_a1, f});
                                  },
                                  [&](const typename LoopifyStructures::nested::
                                          NList &_args0) -> void {
                                    _stack.push_back(_Call2{_args0.d_a0, f});
                                    _stack.push_back(_Enter{_args.d_a1, f});
                                  }},
                              _args.d_a0->v());
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::cons(_f._s0, _result);
            },
            [&](_Call2 _f) {
              _stack.push_back(_Call3{_result});
              _stack.push_back(_Enter{_f._s0, _f._s1});
            },
            [&](_Call3 _f) { _result = _result->app(_f._s0); }},
        _frame);
  }
  return _result;
}

/// find_first_some l finds first Some value in list of options.
__attribute__((pure)) std::optional<unsigned int>
LoopifyStructures::find_first_some(
    const std::shared_ptr<List<std::optional<unsigned int>>> &l) {
  std::optional<unsigned int> _result;
  std::shared_ptr<List<std::optional<unsigned int>>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::optional<unsigned int>>::Nil &) {
              _result = std::optional<unsigned int>();
              _continue = false;
            },
            [&](const typename List<std::optional<unsigned int>>::Cons &_args) {
              if (_args.d_a0.has_value()) {
                unsigned int v = *_args.d_a0;
                _result = std::make_optional<unsigned int>(v);
                _continue = false;
              } else {
                _loop_l = _args.d_a1;
              }
            }},
        _loop_l->v());
  }
  return _result;
}

/// ltree_max t1 t2 element-wise max of two leaf-trees.
std::shared_ptr<LoopifyStructures::ltree>
LoopifyStructures::ltree_max(std::shared_ptr<LoopifyStructures::ltree> t1,
                             std::shared_ptr<LoopifyStructures::ltree> t2) {
  struct _Enter {
    std::shared_ptr<LoopifyStructures::ltree> t2;
    std::shared_ptr<LoopifyStructures::ltree> t1;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyStructures::ltree::LNode &>()
                 .d_a1) _s0;
    decltype(std::declval<const typename LoopifyStructures::ltree::LNode &>()
                 .d_a1) _s1;
    unsigned int _s2;
  };

  struct _Call2 {
    std::shared_ptr<LoopifyStructures::ltree> _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<LoopifyStructures::ltree> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t2, t1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<LoopifyStructures::ltree> t2 = _f.t2;
              std::shared_ptr<LoopifyStructures::ltree> t1 = _f.t1;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyStructures::ltree::LLeaf &_args)
                          -> void {
                        if (t2.use_count() == 1 && t2->v().index() == 0) {
                          auto &_rf = std::get<0>(t2->v_mut());
                          unsigned int y = std::move(_rf.d_a0);
                          _rf.d_a0 = [&]() -> unsigned int {
                            if (_args.d_a0 <= y) {
                              return y;
                            } else {
                              return _args.d_a0;
                            }
                          }();
                          _result = t2;
                        } else {
                          _result = std::visit(
                              Overloaded{
                                  [&](const typename LoopifyStructures::ltree::
                                          LLeaf &_args0)
                                      -> std::shared_ptr<
                                          LoopifyStructures::ltree> {
                                    return ltree::lleaf([&]() -> unsigned int {
                                      if (_args.d_a0 <= _args0.d_a0) {
                                        return _args0.d_a0;
                                      } else {
                                        return _args.d_a0;
                                      }
                                    }());
                                  },
                                  [&](const typename LoopifyStructures::ltree::
                                          LNode &)
                                      -> std::shared_ptr<
                                          LoopifyStructures::ltree> {
                                    return t2;
                                  }},
                              t2->v());
                        }
                      },
                      [&](const typename LoopifyStructures::ltree::LNode &_args)
                          -> void {
                        std::visit(
                            Overloaded{[&](const typename LoopifyStructures::
                                               ltree::LLeaf &) -> void {
                                         _result = std::move(t1);
                                       },
                                       [&](const typename LoopifyStructures::
                                               ltree::LNode &_args0) -> void {
                                         unsigned int max_val;
                                         if (_args.d_a0 <= _args0.d_a0) {
                                           max_val = _args0.d_a0;
                                         } else {
                                           max_val = _args.d_a0;
                                         }
                                         _stack.push_back(_Call1{
                                             _args0.d_a1, _args.d_a1, max_val});
                                         _stack.push_back(
                                             _Enter{_args0.d_a2, _args.d_a2});
                                       }},
                            t2->v());
                      }},
                  t1->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s2});
              _stack.push_back(_Enter{_f._s0, _f._s1});
            },
            [&](_Call2 _f) {
              _result = ltree::lnode(_f._s1, _result, _f._s0);
            }},
        _frame);
  }
  return _result;
}
