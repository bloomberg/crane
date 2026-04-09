#include <loopify_option_maybe.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) std::optional<unsigned int>
LoopifyOptionMaybe::find_even(const std::shared_ptr<List<unsigned int>> &l) {
  std::optional<unsigned int> _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                            _result = std::optional<unsigned int>();
                            _continue = false;
                          },
                          [&](const typename List<unsigned int>::Cons _args) {
                            if ((2u ? _args.d_a0 % 2u : _args.d_a0) == 0u) {
                              _result =
                                  std::make_optional<unsigned int>(_args.d_a0);
                              _continue = false;
                            } else {
                              _loop_l = _args.d_a1;
                            }
                          }},
               _loop_l->v());
  }
  return _result;
}

__attribute__((pure)) std::optional<unsigned int>
LoopifyOptionMaybe::find_greater(const unsigned int threshold,
                                 const std::shared_ptr<List<unsigned int>> &l) {
  std::optional<unsigned int> _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                            _result = std::optional<unsigned int>();
                            _continue = false;
                          },
                          [&](const typename List<unsigned int>::Cons _args) {
                            if (threshold < _args.d_a0) {
                              _result =
                                  std::make_optional<unsigned int>(_args.d_a0);
                              _continue = false;
                            } else {
                              _loop_l = _args.d_a1;
                            }
                          }},
               _loop_l->v());
  }
  return _result;
}

__attribute__((pure)) std::optional<unsigned int> LoopifyOptionMaybe::lookup(
    const unsigned int key,
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l) {
  std::optional<unsigned int> _result;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::pair<unsigned int, unsigned int>>::Nil
                    _args) {
              _result = std::optional<unsigned int>();
              _continue = false;
            },
            [&](const typename List<std::pair<unsigned int, unsigned int>>::Cons
                    _args) {
              unsigned int k = _args.d_a0.first;
              unsigned int v = _args.d_a0.second;
              if (key == k) {
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

std::shared_ptr<List<unsigned int>> LoopifyOptionMaybe::lookup_all(
    const unsigned int key,
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _loop_l = l;
  unsigned int _loop_key = key;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::pair<unsigned int, unsigned int>>::Nil
                    _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<std::pair<unsigned int, unsigned int>>::Cons
                    _args) {
              unsigned int k = _args.d_a0.first;
              unsigned int v = _args.d_a0.second;
              if (_loop_key == k) {
                auto _cell = List<unsigned int>::cons(v, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_l = _args.d_a1;
              } else {
                std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
                    _next_l = _args.d_a1;
                unsigned int _next_key = std::move(_loop_key);
                _loop_l = std::move(_next_l);
                _loop_key = std::move(_next_key);
              }
            }},
        _loop_l->v());
  }
  return _head;
}

__attribute__((pure)) std::optional<unsigned int>
LoopifyOptionMaybe::safe_head(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(Overloaded{[](const typename List<unsigned int>::Nil _args)
                                   -> std::optional<unsigned int> {
                                 return std::optional<unsigned int>();
                               },
                               [](const typename List<unsigned int>::Cons _args)
                                   -> std::optional<unsigned int> {
                                 return std::make_optional<unsigned int>(
                                     _args.d_a0);
                               }},
                    l->v());
}

__attribute__((pure)) std::optional<std::shared_ptr<List<unsigned int>>>
LoopifyOptionMaybe::safe_tail(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args)
              -> std::optional<std::shared_ptr<List<unsigned int>>> {
            return std::optional<std::shared_ptr<List<unsigned int>>>();
          },
          [](const typename List<unsigned int>::Cons _args)
              -> std::optional<std::shared_ptr<List<unsigned int>>> {
            return std::make_optional<std::shared_ptr<List<unsigned int>>>(
                _args.d_a1);
          }},
      l->v());
}

std::shared_ptr<List<unsigned int>> LoopifyOptionMaybe::catMaybes(
    const std::shared_ptr<List<std::optional<unsigned int>>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<std::optional<unsigned int>>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::optional<unsigned int>>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<std::optional<unsigned int>>::Cons _args) {
              if (_args.d_a0.has_value()) {
                unsigned int x = *_args.d_a0;
                auto _cell = List<unsigned int>::cons(x, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_l = _args.d_a1;
              } else {
                _loop_l = _args.d_a1;
              }
            }},
        _loop_l->v());
  }
  return _head;
}

__attribute__((pure)) std::optional<unsigned int>
LoopifyOptionMaybe::find_index_even_aux(
    const std::shared_ptr<List<unsigned int>> &l, const unsigned int idx) {
  std::optional<unsigned int> _result;
  unsigned int _loop_idx = idx;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                     _result = std::optional<unsigned int>();
                     _continue = false;
                   },
                   [&](const typename List<unsigned int>::Cons _args) {
                     if ((2u ? _args.d_a0 % 2u : _args.d_a0) == 0u) {
                       _result = std::make_optional<unsigned int>(_loop_idx);
                       _continue = false;
                     } else {
                       unsigned int _next_idx = (std::move(_loop_idx) + 1u);
                       std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                       _loop_idx = std::move(_next_idx);
                       _loop_l = std::move(_next_l);
                     }
                   }},
        _loop_l->v());
  }
  return _result;
}

__attribute__((pure)) std::optional<unsigned int>
LoopifyOptionMaybe::find_index_even(
    const std::shared_ptr<List<unsigned int>> &l) {
  return find_index_even_aux(l, 0u);
}
