#include <loopify_scans.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
LoopifyScans::scanl(const unsigned int acc,
                    const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::ctor::Cons_(
                    std::move(_loop_acc), List<unsigned int>::ctor::Nil_());
              } else {
                _head = List<unsigned int>::ctor::Cons_(
                    std::move(_loop_acc), List<unsigned int>::ctor::Nil_());
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              auto _cell = List<unsigned int>::ctor::Cons_(_loop_acc, nullptr);
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
              unsigned int _next_acc = (_loop_acc + _args.d_a0);
              _loop_l = std::move(_next_l);
              _loop_acc = std::move(_next_acc);
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyScans::scanl_mult(const unsigned int acc,
                         const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::ctor::Cons_(
                    std::move(_loop_acc), List<unsigned int>::ctor::Nil_());
              } else {
                _head = List<unsigned int>::ctor::Cons_(
                    std::move(_loop_acc), List<unsigned int>::ctor::Nil_());
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              auto _cell = List<unsigned int>::ctor::Cons_(_loop_acc, nullptr);
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
              unsigned int _next_acc = (_loop_acc * _args.d_a0);
              _loop_l = std::move(_next_l);
              _loop_acc = std::move(_next_acc);
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyScans::running_max(const unsigned int current,
                          const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_current = current;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::ctor::Cons_(
                    std::move(_loop_current), List<unsigned int>::ctor::Nil_());
              } else {
                _head = List<unsigned int>::ctor::Cons_(
                    std::move(_loop_current), List<unsigned int>::ctor::Nil_());
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              unsigned int new_max;
              if (_loop_current < _args.d_a0) {
                new_max = _args.d_a0;
              } else {
                new_max = _loop_current;
              }
              auto _cell = List<unsigned int>::ctor::Cons_(
                  std::move(_loop_current), nullptr);
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
              unsigned int _next_current = std::move(new_max);
              _loop_l = std::move(_next_l);
              _loop_current = std::move(_next_current);
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyScans::running_min(const unsigned int current,
                          const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_current = current;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::ctor::Cons_(
                    std::move(_loop_current), List<unsigned int>::ctor::Nil_());
              } else {
                _head = List<unsigned int>::ctor::Cons_(
                    std::move(_loop_current), List<unsigned int>::ctor::Nil_());
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              unsigned int new_min;
              if (_args.d_a0 < _loop_current) {
                new_min = _args.d_a0;
              } else {
                new_min = _loop_current;
              }
              auto _cell = List<unsigned int>::ctor::Cons_(
                  std::move(_loop_current), nullptr);
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
              unsigned int _next_current = std::move(new_min);
              _loop_l = std::move(_next_l);
              _loop_current = std::move(_next_current);
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyScans::pairwise_diff(const unsigned int prev,
                            const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_prev = prev;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::ctor::Nil_();
              } else {
                _head = List<unsigned int>::ctor::Nil_();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              unsigned int diff;
              if (_args.d_a0 < _loop_prev) {
                unsigned int sub = (((_loop_prev - _args.d_a0) > _loop_prev
                                         ? 0
                                         : (_loop_prev - _args.d_a0)));
                if (_loop_prev < sub) {
                  diff = 0u;
                } else {
                  diff = sub;
                }
              } else {
                unsigned int sub = (((_args.d_a0 - _loop_prev) > _args.d_a0
                                         ? 0
                                         : (_args.d_a0 - _loop_prev)));
                if (_args.d_a0 < sub) {
                  diff = 0u;
                } else {
                  diff = sub;
                }
              }
              auto _cell =
                  List<unsigned int>::ctor::Cons_(std::move(diff), nullptr);
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
              unsigned int _next_prev = _args.d_a0;
              _loop_l = std::move(_next_l);
              _loop_prev = std::move(_next_prev);
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyScans::accumulate_if_even(const unsigned int acc,
                                 const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::ctor::Cons_(
                    std::move(_loop_acc), List<unsigned int>::ctor::Nil_());
              } else {
                _head = List<unsigned int>::ctor::Cons_(
                    std::move(_loop_acc), List<unsigned int>::ctor::Nil_());
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              if ((_args.d_a0 % 2u) == 0u) {
                auto _cell =
                    List<unsigned int>::ctor::Cons_(_loop_acc, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                unsigned int _next_acc = (_loop_acc + _args.d_a0);
                _loop_l = std::move(_next_l);
                _loop_acc = std::move(_next_acc);
              } else {
                auto _cell =
                    List<unsigned int>::ctor::Cons_(_loop_acc, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_l = _args.d_a1;
              }
            }},
        _loop_l->v());
  }
  return _head;
}
