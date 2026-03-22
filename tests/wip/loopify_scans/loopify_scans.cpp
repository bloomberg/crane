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
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int acc;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, acc});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     const unsigned int acc = _f.acc;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> void {
                               _result = List<unsigned int>::ctor::Cons_(
                                   std::move(acc),
                                   List<unsigned int>::ctor::Nil_());
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               _stack.push_back(_Call1{acc});
                               _stack.push_back(
                                   _Enter{_args.d_a1, (acc + _args.d_a0)});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) {
                     _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
                   }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyScans::scanl_mult(const unsigned int acc,
                         const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int acc;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, acc});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     const unsigned int acc = _f.acc;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> void {
                               _result = List<unsigned int>::ctor::Cons_(
                                   std::move(acc),
                                   List<unsigned int>::ctor::Nil_());
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               _stack.push_back(_Call1{acc});
                               _stack.push_back(
                                   _Enter{_args.d_a1, (acc * _args.d_a0)});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) {
                     _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
                   }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyScans::running_max(const unsigned int current,
                          const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int current;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, current});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     const unsigned int current = _f.current;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> void {
                               _result = List<unsigned int>::ctor::Cons_(
                                   std::move(current),
                                   List<unsigned int>::ctor::Nil_());
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               unsigned int new_max;
                               if (current < _args.d_a0) {
                                 new_max = _args.d_a0;
                               } else {
                                 new_max = current;
                               }
                               _stack.push_back(_Call1{std::move(current)});
                               _stack.push_back(
                                   _Enter{_args.d_a1, std::move(new_max)});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) {
                     _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
                   }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyScans::running_min(const unsigned int current,
                          const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int current;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, current});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     const unsigned int current = _f.current;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> void {
                               _result = List<unsigned int>::ctor::Cons_(
                                   std::move(current),
                                   List<unsigned int>::ctor::Nil_());
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               unsigned int new_min;
                               if (_args.d_a0 < current) {
                                 new_min = _args.d_a0;
                               } else {
                                 new_min = current;
                               }
                               _stack.push_back(_Call1{std::move(current)});
                               _stack.push_back(
                                   _Enter{_args.d_a1, std::move(new_min)});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) {
                     _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
                   }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyScans::pairwise_diff(const unsigned int prev,
                            const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int prev;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, prev});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     const unsigned int prev = _f.prev;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> void {
                               _result = List<unsigned int>::ctor::Nil_();
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               unsigned int diff;
                               if (_args.d_a0 < prev) {
                                 unsigned int sub =
                                     (((prev - _args.d_a0) > prev
                                           ? 0
                                           : (prev - _args.d_a0)));
                                 if (prev < sub) {
                                   diff = 0u;
                                 } else {
                                   diff = sub;
                                 }
                               } else {
                                 unsigned int sub =
                                     (((_args.d_a0 - prev) > _args.d_a0
                                           ? 0
                                           : (_args.d_a0 - prev)));
                                 if (_args.d_a0 < sub) {
                                   diff = 0u;
                                 } else {
                                   diff = sub;
                                 }
                               }
                               _stack.push_back(_Call1{std::move(diff)});
                               _stack.push_back(_Enter{_args.d_a1, _args.d_a0});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) {
                     _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
                   }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyScans::accumulate_if_even(const unsigned int acc,
                                 const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int acc;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  struct _Call2 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, acc});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     const unsigned int acc = _f.acc;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> void {
                               _result = List<unsigned int>::ctor::Cons_(
                                   std::move(acc),
                                   List<unsigned int>::ctor::Nil_());
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               if ((_args.d_a0 % 2u) == 0u) {
                                 _stack.push_back(_Call1{acc});
                                 _stack.push_back(
                                     _Enter{_args.d_a1, (acc + _args.d_a0)});
                               } else {
                                 _stack.push_back(_Call2{acc});
                                 _stack.push_back(_Enter{_args.d_a1, acc});
                               }
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) {
                     _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
                   },
                   [&](_Call2 _f) {
                     _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
                   }},
        _frame);
  }
  return _result;
}
