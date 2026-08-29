#ifndef INCLUDED_REUSE_MAP_TYPE_CHANGE
#define INCLUDED_REUSE_MAP_TYPE_CHANGE

#include "rc.h"
#include "small_vector.h"
#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct ReuseMapTypeChange {
  template <typename A> struct lst {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      crane::rc<lst<A>> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    lst() {}

    explicit lst(Nil _v) : v_(_v) {}

    explicit lst(Cons _v) : v_(std::move(_v)) {}

    template <typename _U> lst(const lst<_U> &_other) {
      if (std::holds_alternative<typename lst<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a0, a1] = std::get<typename lst<_U>::Cons>(_other.v());
        this->v_ = Cons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
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
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? crane::make_rc<lst<A>>(*a1) : nullptr};
      }
    }

    static lst<A> nil() { return lst<A>(Nil{}); }

    static lst<A> cons(A a0, lst<A> a1) {
      return lst<A>(Cons{std::move(a0), crane::make_rc<lst<A>>(std::move(a1))});
    }

    static lst<A> cons__reuse(crane::rc<lst<A>> _tok, A a0, lst<A> a1) {
      return lst<A>(Cons{std::move(a0), crane::make_rc_reusing<lst<A>>(
                                            std::move(_tok), std::move(a1))});
    }

    // MANIPULATORS
    ~lst() {
      crane::small_vector<crane::rc<lst<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
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

    lst(const lst &) = default;
    lst &operator=(const lst &) = default;
    lst(lst &&) noexcept = default;
    lst &operator=(lst &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, lst<T1> &, T2 &>
  static T2 lst_rect(T2 f, F1 &&f0, const lst<T1> &l) {
    if (std::holds_alternative<typename lst<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename lst<T1>::Cons>(l.v());
      return f0(a0, *a1, lst_rect<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, lst<T1> &, T2 &>
  static T2 lst_rec(T2 f, F1 &&f0, const lst<T1> &l) {
    if (std::holds_alternative<typename lst<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename lst<T1>::Cons>(l.v());
      return f0(a0, *a1, lst_rec<T1, T2>(f, f0, *a1));
    }
  }

  static lst<uint64_t> build(uint64_t n, lst<uint64_t> acc);
  static uint64_t suml(const lst<uint64_t> &l);

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static lst<T2> mapl(F0 &&f, lst<T1> l) {
    if (std::holds_alternative<typename lst<T1>::Nil>(l.v_mut())) {
      return lst<T2>::nil();
    } else {
      auto &[a0, a1] = std::get<typename lst<T1>::Cons>(l.v_mut());
      return lst<T2>::cons(f(std::move(a0)), mapl<T1, T2>(f, *a1));
    }
  }

  static uint64_t go1(uint64_t n);
  static uint64_t go2(uint64_t n);
};

#endif // INCLUDED_REUSE_MAP_TYPE_CHANGE
