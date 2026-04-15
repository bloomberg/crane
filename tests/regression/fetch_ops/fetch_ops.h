#ifndef INCLUDED_FETCH_OPS
#define INCLUDED_FETCH_OPS

#include <memory>
#include <optional>
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
  explicit List(Nil _v) : d_v_(_v) {}

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

  t_A nth(const unsigned int n, const t_A default0) const {
    if (n <= 0) {
      if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
        return default0;
      } else {
        const auto &_m = *std::get_if<typename List<t_A>::Cons>(&this->v());
        return _m.d_a0;
      }
    } else {
      unsigned int m = n - 1;
      if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
        return default0;
      } else {
        const auto &_m0 = *std::get_if<typename List<t_A>::Cons>(&this->v());
        return _m0.d_a1->nth(m, default0);
      }
    }
  }
};

struct FetchOps {
  struct state {
    std::shared_ptr<List<unsigned int>> rom;
  };

  __attribute__((pure)) static unsigned int
  fetch_byte(const std::shared_ptr<state> &s, const unsigned int addr);
  static inline const unsigned int fetch_default_test = fetch_byte(
      std::make_shared<state>(state{List<unsigned int>::cons(
          1u, List<unsigned int>::cons(2u, List<unsigned int>::nil()))}),
      5u);
  __attribute__((pure)) static unsigned int
  fetch_byte_direct(const std::shared_ptr<List<unsigned int>> &rom_data,
                    const unsigned int addr);
  static inline const unsigned int fetch_in_range_test = fetch_byte_direct(
      List<unsigned int>::cons(
          11u,
          List<unsigned int>::cons(
              22u, List<unsigned int>::cons(33u, List<unsigned int>::nil()))),
      1u);

  template <typename T1>
  static std::shared_ptr<List<T1>> drop(const unsigned int n,
                                        std::shared_ptr<List<T1>> l) {
    if (n <= 0) {
      return l;
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l->v()) &&
          l.use_count() == 1) {
        return l;
      } else if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
        return List<T1>::nil();
      } else {
        const auto &_m = *std::get_if<typename List<T1>::Cons>(&l->v());
        return drop<T1>(n_, _m.d_a1);
      }
    }
  }

  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  fetch_pair(const std::shared_ptr<List<unsigned int>> &rom_data,
             const unsigned int addr);
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
  fetch_window(const std::shared_ptr<List<unsigned int>> &rom_data,
               const unsigned int addr);
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

#endif // INCLUDED_FETCH_OPS
