#ifndef INCLUDED_LOOPIFY_COIND_COLIST
#define INCLUDED_LOOPIFY_COIND_COLIST

#include "lazy.h"
#include <functional>
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

struct LoopifyCoindColist {
  template <typename t_A> struct colist {
    // TYPES
    struct Conil {};

    struct Cocons {
      t_A d_a0;
      std::shared_ptr<colist<t_A>> d_a1;
    };

    using variant_t = std::variant<Conil, Cocons>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

  public:
    // CREATORS
    explicit colist(Conil _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(Cocons _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static std::shared_ptr<colist<t_A>> conil() {
      return std::make_shared<colist<t_A>>(Conil{});
    }

    static std::shared_ptr<colist<t_A>>
    cocons(t_A a0, const std::shared_ptr<colist<t_A>> &a1) {
      return std::make_shared<colist<t_A>>(Cocons{std::move(a0), a1});
    }

    static std::shared_ptr<colist<t_A>>
    cocons(t_A a0, std::shared_ptr<colist<t_A>> &&a1) {
      return std::make_shared<colist<t_A>>(
          Cocons{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<colist<t_A>>
    lazy_(std::function<std::shared_ptr<colist<t_A>>()> thunk) {
      return std::make_shared<colist<t_A>>(
          std::function<variant_t()>([=]() mutable -> variant_t {
            std::shared_ptr<colist<t_A>> _tmp = thunk();
            return _tmp->v();
          }));
    }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<colist<T2>>
  comap(F0 &&f, const std::shared_ptr<colist<T1>> &l) {
    return colist<T2>::lazy_([=]() mutable -> std::shared_ptr<colist<T2>> {
      return std::visit(Overloaded{[](const typename colist<T1>::Conil _args)
                                       -> std::shared_ptr<colist<T2>> {
                                     return colist<T2>::conil();
                                   },
                                   [&](const typename colist<T1>::Cocons _args)
                                       -> std::shared_ptr<colist<T2>> {
                                     return colist<T2>::cocons(
                                         f(_args.d_a0),
                                         comap<T1, T2>(f, _args.d_a1));
                                   }},
                        l->v());
    });
  }

  template <typename T1>
  static std::shared_ptr<colist<T1>>
  cotake(const unsigned int n, const std::shared_ptr<colist<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<colist<T1>> l;
      const unsigned int n;
    };

    using _Frame = std::variant<_Enter>;
    std::shared_ptr<colist<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l, n});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
            const std::shared_ptr<colist<T1>> l = _f.l;
            const unsigned int n = _f.n;
            if (n <= 0) {
              _result = colist<T1>::lazy_([]() -> std::shared_ptr<colist<T1>> {
                return colist<T1>::conil();
              });
            } else {
              unsigned int n_ = n - 1;
              _result = colist<T1>::lazy_(
                  [=]() mutable -> std::shared_ptr<colist<T1>> {
                    return std::visit(
                        Overloaded{[](const typename colist<T1>::Conil _args)
                                       -> std::shared_ptr<colist<T1>> {
                                     return colist<T1>::conil();
                                   },
                                   [&](const typename colist<T1>::Cocons _args)
                                       -> std::shared_ptr<colist<T1>> {
                                     return colist<T1>::cocons(
                                         _args.d_a0,
                                         cotake<T1>(n_, _args.d_a1));
                                   }},
                        l->v());
                  });
            }
          }},
          _frame);
    }
    return _result;
  }

  template <typename T1>
  static std::shared_ptr<colist<T1>>
  from_list(const std::shared_ptr<List<T1>> &l) {
    return colist<T1>::lazy_([=]() mutable -> std::shared_ptr<colist<T1>> {
      return std::visit(Overloaded{[](const typename List<T1>::Nil _args)
                                       -> std::shared_ptr<colist<T1>> {
                                     return colist<T1>::conil();
                                   },
                                   [](const typename List<T1>::Cons _args)
                                       -> std::shared_ptr<colist<T1>> {
                                     return colist<T1>::cocons(
                                         _args.d_a0, from_list<T1>(_args.d_a1));
                                   }},
                        l->v());
    });
  }

  template <typename T1>
  static std::shared_ptr<List<T1>>
  to_list(const unsigned int fuel, const std::shared_ptr<colist<T1>> &l) {
    std::shared_ptr<List<T1>> _head{};
    std::shared_ptr<List<T1>> _last{};
    std::shared_ptr<colist<T1>> _loop_l = l;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        {
          if (_last) {
            std::get<typename List<T1>::Cons>(_last->v_mut()).d_a1 =
                List<T1>::nil();
          } else {
            _head = List<T1>::nil();
          }
          _continue = false;
        }
      } else {
        unsigned int f = _loop_fuel - 1;
        std::visit(
            Overloaded{
                [&](const typename colist<T1>::Conil _args) {
                  if (_last) {
                    std::get<typename List<T1>::Cons>(_last->v_mut()).d_a1 =
                        List<T1>::nil();
                  } else {
                    _head = List<T1>::nil();
                  }
                  _continue = false;
                },
                [&](const typename colist<T1>::Cocons _args) {
                  auto _cell = List<T1>::cons(_args.d_a0, nullptr);
                  if (_last) {
                    std::get<typename List<T1>::Cons>(_last->v_mut()).d_a1 =
                        _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  std::shared_ptr<colist<T1>> _next_l = _args.d_a1;
                  unsigned int _next_fuel = f;
                  _loop_l = std::move(_next_l);
                  _loop_fuel = std::move(_next_fuel);
                }},
            _loop_l->v());
      }
    }
    return _head;
  }

  static inline const std::shared_ptr<List<unsigned int>> test_comap =
      to_list<unsigned int>(
          5u, comap<unsigned int, unsigned int>(
                  [](unsigned int n) { return (n * 2u); },
                  from_list<unsigned int>(List<unsigned int>::cons(
                      1u, List<unsigned int>::cons(
                              2u, List<unsigned int>::cons(
                                      3u, List<unsigned int>::nil()))))));
  static inline const std::shared_ptr<List<unsigned int>> test_cotake =
      to_list<unsigned int>(
          10u,
          cotake<unsigned int>(
              2u, from_list<unsigned int>(List<unsigned int>::cons(
                      10u, List<unsigned int>::cons(
                               20u, List<unsigned int>::cons(
                                        30u, List<unsigned int>::nil()))))));
};

#endif // INCLUDED_LOOPIFY_COIND_COLIST
