#ifndef INCLUDED_UPDATE_NTH_BOUNDS
#define INCLUDED_UPDATE_NTH_BOUNDS

#include <any>
#include <memory>
#include <utility>
#include <variant>

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
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> skipn(uint64_t n) const {
    if (n <= 0) {
      return std::move(*this);
    } else {
      uint64_t n0 = n - 1;
      if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
        return List<A>::nil();
      } else {
        auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
        return a1->skipn(n0);
      }
    }
  }

  List<A> firstn(uint64_t n) const {
    if (n <= 0) {
      return List<A>::nil();
    } else {
      uint64_t n0 = n - 1;
      if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
        return List<A>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
        return List<A>::cons(a0, a1->firstn(n0));
      }
    }
  }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
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

struct UpdateNthBounds {
  template <typename T1>
  static List<T1> update_nth(uint64_t n, T1 x, List<T1> l) {
    if (n < l.length()) {
      return l.firstn(n).app(List<T1>::cons(x, l.skipn((n + 1))));
    } else {
      return l;
    }
  }

  static inline const uint64_t in_bounds_length =
      update_nth<uint64_t>(
          UINT64_C(2), UINT64_C(9),
          List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(
                  UINT64_C(2),
                  List<uint64_t>::cons(
                      UINT64_C(3), List<uint64_t>::cons(
                                       UINT64_C(4), List<uint64_t>::nil())))))
          .length();
  static inline const uint64_t out_of_bounds_length =
      update_nth<uint64_t>(
          UINT64_C(9), UINT64_C(7),
          List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(
                  UINT64_C(2),
                  List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))))
          .length();
};

#endif // INCLUDED_UPDATE_NTH_BOUNDS
