#ifndef INCLUDED_LOOPIFY_COIND_COLIST
#define INCLUDED_LOOPIFY_COIND_COLIST

#include "lazy.h"
#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct LoopifyCoindColist {
  template <typename A> struct colist {
    // TYPES
    struct Conil {};

    struct Cocons {
      A a0;
      std::shared_ptr<colist<A>> a1;
    };

    using variant_t = std::variant<Conil, Cocons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    explicit colist(Conil _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(Cocons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static colist<A> conil() { return colist(Conil{}); }

    static colist<A> cocons(A a0, const colist<A> &a1) {
      return colist(Cocons{std::move(a0), std::make_shared<colist<A>>(a1)});
    }

    static colist<A> lazy_(std::function<colist<A>()> thunk) {
      return colist<A>(std::function<variant_t()>([=]() mutable -> variant_t {
        colist<A> _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }
  };

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static colist<T2> comap(F0 &&f, colist<T1> l) {
    if (std::holds_alternative<typename colist<T1>::Conil>(l.v())) {
      return colist<T2>::lazy_(
          []() -> colist<T2> { return colist<T2>::conil(); });
    } else {
      const auto &[a0, a1] = std::get<typename colist<T1>::Cocons>(l.v());
      return colist<T2>::lazy_([=]() mutable -> colist<T2> {
        return colist<T2>::cocons(f(a0), comap<T1, T2>(f, *a1));
      });
    }
  }

  template <typename T1> static colist<T1> cotake(uint64_t n, colist<T1> l) {
    if (n <= 0) {
      return colist<T1>::lazy_(
          []() -> colist<T1> { return colist<T1>::conil(); });
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename colist<T1>::Conil>(l.v())) {
        return colist<T1>::lazy_(
            []() -> colist<T1> { return colist<T1>::conil(); });
      } else {
        const auto &[a0, a1] = std::get<typename colist<T1>::Cocons>(l.v());
        return colist<T1>::lazy_([=]() mutable -> colist<T1> {
          return colist<T1>::cocons(a0, cotake<T1>(n_, *a1));
        });
      }
    }
  }

  template <typename T1> static colist<T1> from_list(const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return colist<T1>::lazy_(
          []() -> colist<T1> { return colist<T1>::conil(); });
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      const List<T1> &a1_value = *a1;
      return colist<T1>::lazy_([=]() mutable -> colist<T1> {
        return colist<T1>::cocons(a0, from_list<T1>(a1_value));
      });
    }
  }

  template <typename T1>
  static List<T1>
  to_list(uint64_t fuel,
          colist<T1> l) { /// _Enter: captures varying parameters for each
                          /// recursive call.

    struct _Enter {
      colist<T1> l;
      uint64_t fuel;
    };

    /// _Resume_Cocons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cocons {
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cocons>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{std::move(l), fuel});
    /// Loopified to_list: _Enter -> _Resume_Cocons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        colist<T1> l = std::move(_f.l);
        uint64_t fuel = _f.fuel;
        if (fuel <= 0) {
          _result = List<T1>::nil();
        } else {
          uint64_t f = fuel - 1;
          if (std::holds_alternative<typename colist<T1>::Conil>(l.v())) {
            _result = List<T1>::nil();
          } else {
            const auto &[a0, a1] = std::get<typename colist<T1>::Cocons>(l.v());
            _stack.emplace_back(_Resume_Cocons{a0});
            _stack.emplace_back(_Enter{*a1, f});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cocons>(_frame));
        _result = List<T1>::cons(std::move(_f.a0), std::move(_result));
      }
    }
    return _result;
  }

  static inline const List<uint64_t> test_comap = to_list<uint64_t>(
      UINT64_C(5),
      comap<uint64_t, uint64_t>(
          [](uint64_t n) { return (n * UINT64_C(2)); },
          from_list<uint64_t>(List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(
                  UINT64_C(2),
                  List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))))));
  static inline const List<uint64_t> test_cotake = to_list<uint64_t>(
      UINT64_C(10),
      cotake<uint64_t>(
          UINT64_C(2),
          from_list<uint64_t>(List<uint64_t>::cons(
              UINT64_C(10),
              List<uint64_t>::cons(
                  UINT64_C(20), List<uint64_t>::cons(
                                    UINT64_C(30), List<uint64_t>::nil()))))));
};

#endif // INCLUDED_LOOPIFY_COIND_COLIST
