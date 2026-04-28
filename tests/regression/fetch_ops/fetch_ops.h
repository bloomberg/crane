#ifndef INCLUDED_FETCH_OPS
#define INCLUDED_FETCH_OPS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct ListDef {
  template <typename T1>
  static T1 nth(const unsigned int &n, const List<T1> &l, const T1 default0);
};

struct FetchOps {
  struct state {
    List<unsigned int> rom;

    // ACCESSORS
    __attribute__((pure)) state clone() const {
      return state{(*(this)).rom.clone()};
    }
  };

  __attribute__((pure)) static unsigned int
  fetch_byte(const state &s, const unsigned int &addr);
  static inline const unsigned int fetch_default_test = fetch_byte(
      state{List<unsigned int>::cons(
          1u, List<unsigned int>::cons(2u, List<unsigned int>::nil()))},
      5u);
  __attribute__((pure)) static unsigned int
  fetch_byte_direct(const List<unsigned int> &rom_data,
                    const unsigned int &addr);
  static inline const unsigned int fetch_in_range_test = fetch_byte_direct(
      List<unsigned int>::cons(
          11u,
          List<unsigned int>::cons(
              22u, List<unsigned int>::cons(33u, List<unsigned int>::nil()))),
      1u);

  template <typename T1>
  __attribute__((pure)) static List<T1> drop(const unsigned int &n,
                                             List<T1> l) {
    if (n <= 0) {
      return l;
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v_mut())) {
        return List<T1>::nil();
      } else {
        auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v_mut());
        return drop<T1>(n_, *(d_a1));
      }
    }
  }

  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  fetch_pair(const List<unsigned int> &rom_data, const unsigned int &addr);
  static inline const unsigned int fetch_pair_test = []() {
    std::pair<unsigned int, unsigned int> p = fetch_pair(
        List<unsigned int>::cons(
            1u,
            List<unsigned int>::cons(
                2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))),
        0u);
    return (p.first + p.second);
  }();
  __attribute__((
      pure)) static std::optional<std::pair<unsigned int, unsigned int>>
  fetch_window(const List<unsigned int> &rom_data, const unsigned int &addr);
  static inline const unsigned int fetch_window_test = []() -> unsigned int {
    auto _cs = fetch_window(
        List<unsigned int>::cons(
            9u,
            List<unsigned int>::cons(
                8u, List<unsigned int>::cons(7u, List<unsigned int>::nil()))),
        0u);
    if (_cs.has_value()) {
      const std::pair<unsigned int, unsigned int> &p = *_cs;
      const unsigned int &_x = p.first;
      const unsigned int &next = p.second;
      return next;
    } else {
      return 0u;
    }
  }();
  static inline const std::pair<
      std::pair<std::pair<unsigned int, unsigned int>, unsigned int>,
      unsigned int>
      t = std::make_pair(std::make_pair(std::make_pair(fetch_default_test,
                                                       fetch_in_range_test),
                                        fetch_pair_test),
                         fetch_window_test);
};

template <typename T1>
T1 ListDef::nth(const unsigned int &n, const List<T1> &l, const T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      return d_a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *(d_a10), default0);
    }
  }
}

#endif // INCLUDED_FETCH_OPS
