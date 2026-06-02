#ifndef INCLUDED_FETCH_OPS
#define INCLUDED_FETCH_OPS

#include <any>
#include <memory>
#include <optional>
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
};

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct FetchOps {
  struct state {
    List<uint64_t> rom;
  };

  static uint64_t fetch_byte(const state &s, uint64_t addr);
  static inline const uint64_t fetch_default_test =
      fetch_byte(state{List<uint64_t>::cons(
                     UINT64_C(1),
                     List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil()))},
                 UINT64_C(5));
  static uint64_t fetch_byte_direct(const List<uint64_t> &rom_data,
                                    uint64_t addr);
  static inline const uint64_t fetch_in_range_test = fetch_byte_direct(
      List<uint64_t>::cons(
          UINT64_C(11),
          List<uint64_t>::cons(
              UINT64_C(22),
              List<uint64_t>::cons(UINT64_C(33), List<uint64_t>::nil()))),
      UINT64_C(1));

  template <typename T1> static List<T1> drop(uint64_t n, List<T1> l) {
    if (n <= 0) {
      return l;
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v_mut())) {
        return List<T1>::nil();
      } else {
        auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v_mut());
        return drop<T1>(n_, *a1);
      }
    }
  }

  static std::pair<uint64_t, uint64_t>
  fetch_pair(const List<uint64_t> &rom_data, uint64_t addr);
  static inline const uint64_t fetch_pair_test = []() {
    std::pair<uint64_t, uint64_t> p = fetch_pair(
        List<uint64_t>::cons(
            UINT64_C(1),
            List<uint64_t>::cons(
                UINT64_C(2),
                List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))),
        UINT64_C(0));
    return (p.first + p.second);
  }();
  static std::optional<std::pair<uint64_t, uint64_t>>
  fetch_window(const List<uint64_t> &rom_data, uint64_t addr);
  static inline const uint64_t fetch_window_test = []() -> uint64_t {
    auto _cs = fetch_window(
        List<uint64_t>::cons(
            UINT64_C(9),
            List<uint64_t>::cons(
                UINT64_C(8),
                List<uint64_t>::cons(UINT64_C(7), List<uint64_t>::nil()))),
        UINT64_C(0));
    if (_cs.has_value()) {
      const std::pair<uint64_t, uint64_t> &p = *_cs;
      const uint64_t &_x = p.first;
      const uint64_t &next = p.second;
      return next;
    } else {
      return UINT64_C(0);
    }
  }();
  static inline const std::pair<
      std::pair<std::pair<uint64_t, uint64_t>, uint64_t>, uint64_t>
      t = std::make_pair(std::make_pair(std::make_pair(fetch_default_test,
                                                       fetch_in_range_test),
                                        fetch_pair_test),
                         fetch_window_test);
};

template <typename T1>
T1 ListDef::nth(uint64_t n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, default0);
    }
  }
}

#endif // INCLUDED_FETCH_OPS
