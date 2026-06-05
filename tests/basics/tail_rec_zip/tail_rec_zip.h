#ifndef INCLUDED_TAIL_REC_ZIP
#define INCLUDED_TAIL_REC_ZIP

#include <any>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

template <typename A, typename B> struct Prod {
  // DATA
  A a0;
  B a1;

  // ACCESSORS
  Prod<A, B> clone() const { return {a0, a1}; }

  // CREATORS
  static Prod<A, B> pair(A a0, B a1) { return {std::move(a0), std::move(a1)}; }
};

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

  List<A> rev() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<A>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return a1->rev().app(List<A>::cons(a0, List<A>::nil()));
    }
  }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

template <typename T1, typename T2>
List<Prod<T1, T2>> better_zip(const List<T1> &la, const List<T2> &lb) {
  auto go_impl = [](auto &_self_go, const List<T1> &la0, const List<T2> &lb0,
                    List<Prod<T1, T2>> acc) -> List<Prod<T1, T2>> {
    if (std::holds_alternative<typename List<T1>::Nil>(la0.v())) {
      return std::move(acc).rev();
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(la0.v());
      if (std::holds_alternative<typename List<T2>::Nil>(lb0.v())) {
        return std::move(acc).rev();
      } else {
        const auto &[a00, a10] = std::get<typename List<T2>::Cons>(lb0.v());
        return _self_go(_self_go, *a1, *a10,
                        List<Prod<T1, T2>>::cons(Prod<T1, T2>::pair(a0, a00),
                                                 std::move(acc)));
      }
    }
  };
  auto go = [&](const List<T1> &la0, const List<T2> &lb0,
                List<Prod<T1, T2>> acc) -> List<Prod<T1, T2>> {
    return go_impl(go_impl, la0, lb0, acc);
  };
  return go(la, lb, List<Prod<T1, T2>>::nil());
}

#endif // INCLUDED_TAIL_REC_ZIP
