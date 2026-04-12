#ifndef INCLUDED_LOOPIFY_EXTREMA
#define INCLUDED_LOOPIFY_EXTREMA

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct LoopifyExtrema {
  __attribute__((pure)) static unsigned int
  maximum(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  minimum(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  minmax(const std::shared_ptr<List<unsigned int>> &l);

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  max_by(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const typename List<unsigned int>::Cons _s0;
      F0 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil &) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<unsigned int>::Cons &_args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil &)
                                      -> void { _result = f(_args.d_a0); },
                                  [&](const typename List<unsigned int>::Cons &)
                                      -> void {
                                    _stack.push_back(_Call1{_args, f});
                                    _stack.push_back(_Enter{_args.d_a1});
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                F0 f = _f._s1;
                unsigned int rest_max = _result;
                unsigned int fx = f(_args.d_a0);
                if (rest_max < fx) {
                  _result = fx;
                } else {
                  _result = rest_max;
                }
              }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  min_by(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const typename List<unsigned int>::Cons _s0;
      F0 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil &) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<unsigned int>::Cons &_args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil &)
                                      -> void { _result = f(_args.d_a0); },
                                  [&](const typename List<unsigned int>::Cons &)
                                      -> void {
                                    _stack.push_back(_Call1{_args, f});
                                    _stack.push_back(_Enter{_args.d_a1});
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                F0 f = _f._s1;
                unsigned int rest_min = _result;
                unsigned int fx = f(_args.d_a0);
                if (fx < rest_min) {
                  _result = fx;
                } else {
                  _result = rest_min;
                }
              }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  argmax(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const typename List<unsigned int>::Cons _s0;
      F0 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil &) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<unsigned int>::Cons &_args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil &)
                                      -> void { _result = _args.d_a0; },
                                  [&](const typename List<unsigned int>::Cons &)
                                      -> void {
                                    _stack.push_back(_Call1{_args, f});
                                    _stack.push_back(_Enter{_args.d_a1});
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                F0 f = _f._s1;
                unsigned int rest_best = _result;
                unsigned int fx = f(_args.d_a0);
                unsigned int f_rest = f(rest_best);
                if (f_rest < fx) {
                  _result = _args.d_a0;
                } else {
                  _result = rest_best;
                }
              }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  argmin(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const typename List<unsigned int>::Cons _s0;
      F0 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil &) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<unsigned int>::Cons &_args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil &)
                                      -> void { _result = _args.d_a0; },
                                  [&](const typename List<unsigned int>::Cons &)
                                      -> void {
                                    _stack.push_back(_Call1{_args, f});
                                    _stack.push_back(_Enter{_args.d_a1});
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                F0 f = _f._s1;
                unsigned int rest_best = _result;
                unsigned int fx = f(_args.d_a0);
                unsigned int f_rest = f(rest_best);
                if (fx < f_rest) {
                  _result = _args.d_a0;
                } else {
                  _result = rest_best;
                }
              }},
          _frame);
    }
    return _result;
  }

  __attribute__((pure)) static unsigned int
  lex_compare(const std::shared_ptr<List<unsigned int>> &l1,
              const std::shared_ptr<List<unsigned int>> &l2);
  __attribute__((pure)) static bool
  all_equal(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static bool
  is_sorted(const std::shared_ptr<List<unsigned int>> &l);

  template <MapsTo<bool, unsigned int, unsigned int> F0>
  __attribute__((pure)) static bool
  adjacent_all(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    bool _result;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil &) {
                _result = true;
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons &_args) {
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil &) {
                          _result = true;
                          _continue = false;
                        },
                        [&](const typename List<unsigned int>::Cons &_args0) {
                          if (p(_args.d_a0, _args0.d_a0)) {
                            _loop_l = _args.d_a1;
                          } else {
                            _result = false;
                            _continue = false;
                          }
                        }},
                    _args.d_a1->v());
              }},
          _loop_l->v());
    }
    return _result;
  }
};

#endif // INCLUDED_LOOPIFY_EXTREMA
