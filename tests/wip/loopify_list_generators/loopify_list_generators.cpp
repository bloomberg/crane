#include <loopify_list_generators.h>

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

std::shared_ptr<List<unsigned int>> LoopifyListGenerators::cycle_fuel(
    const unsigned int fuel, const unsigned int n,
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    const std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const unsigned int n = _f.n;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = List<unsigned int>::ctor::Nil_();
              } else {
                unsigned int fuel_ = fuel - 1;
                if (n <= 0) {
                  _result = List<unsigned int>::ctor::Nil_();
                } else {
                  unsigned int n_ = n - 1;
                  std::visit(
                      Overloaded{
                          [&](const typename List<unsigned int>::Nil _args)
                              -> void {
                            _result = List<unsigned int>::ctor::Nil_();
                          },
                          [&](const typename List<unsigned int>::Cons _args)
                              -> void {
                            _stack.push_back(_Call1{l});
                            _stack.push_back(_Enter{n_, fuel_});
                          }},
                      l->v());
                }
              }
            },
            [&](_Call1 _f) { _result = _f._s0->app(_result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListGenerators::cycle(const unsigned int n,
                             const std::shared_ptr<List<unsigned int>> &l) {
  return cycle_fuel((n * l->length()), n, l);
}

std::shared_ptr<List<unsigned int>>
LoopifyListGenerators::range(const unsigned int start,
                             const unsigned int count) {
  struct _Enter {
    const unsigned int count;
    const unsigned int start;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{count, start});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int count = _f.count;
                            const unsigned int start = _f.start;
                            if (count <= 0) {
                              _result = List<unsigned int>::ctor::Nil_();
                            } else {
                              unsigned int count_ = count - 1;
                              _stack.push_back(_Call1{start});
                              _stack.push_back(_Enter{count_, (start + 1u)});
                            }
                          },
                          [&](_Call1 _f) {
                            _result = List<unsigned int>::ctor::Cons_(_f._s0,
                                                                      _result);
                          }},
               _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListGenerators::replicate_elem(const unsigned int n,
                                      const unsigned int x) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = List<unsigned int>::ctor::Nil_();
                            } else {
                              unsigned int n_ = n - 1;
                              _stack.push_back(_Call1{x});
                              _stack.push_back(_Enter{std::move(n_)});
                            }
                          },
                          [&](_Call1 _f) {
                            _result = List<unsigned int>::ctor::Cons_(_f._s0,
                                                                      _result);
                          }},
               _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListGenerators::replicate_each(
    const unsigned int n, const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> void {
                               _result = List<unsigned int>::ctor::Nil_();
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               std::shared_ptr<List<unsigned int>> reps =
                                   replicate_elem(n, _args.d_a0);
                               _stack.push_back(_Call1{std::move(reps)});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = _f._s0->app(_result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListGenerators::enumerate_aux(
    const unsigned int idx, const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int idx;
  };

  struct _Call1 {
    decltype(std::make_pair(
        std::declval<const unsigned int &>(),
        std::declval<const typename List<unsigned int>::Cons &>().d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, idx});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              const unsigned int idx = _f.idx;
              std::visit(
                  Overloaded{[&](const typename List<unsigned int>::Nil _args)
                                 -> void {
                               _result =
                                   List<std::pair<unsigned int,
                                                  unsigned int>>::ctor::Nil_();
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               _stack.push_back(
                                   _Call1{std::make_pair(idx, _args.d_a0)});
                               _stack.push_back(_Enter{_args.d_a1, (idx + 1u)});
                             }},
                  l->v());
            },
            [&](_Call1 _f) {
              _result =
                  List<std::pair<unsigned int, unsigned int>>::ctor::Cons_(
                      _f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListGenerators::enumerate(const std::shared_ptr<List<unsigned int>> &l) {
  return enumerate_aux(0u, l);
}
