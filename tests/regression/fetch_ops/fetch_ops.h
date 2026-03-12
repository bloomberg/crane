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

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename A> struct List {
  // TYPES
  struct nil {};

  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };

  using variant_t = std::variant<nil, cons>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit List(nil _v) : v_(std::move(_v)) {}

  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }

    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  A nth(const unsigned int n, const A default0) const {
    if (n <= 0) {
      return std::visit(Overloaded{[&](const typename List<A>::nil _args) -> A {
                                     return default0;
                                   },
                                   [](const typename List<A>::cons _args) -> A {
                                     A x = _args._a0;
                                     return x;
                                   }},
                        this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{
              [&](const typename List<A>::nil _args) -> A { return default0; },
              [&](const typename List<A>::cons _args) -> A {
                std::shared_ptr<List<A>> l_ = _args._a1;
                return std::move(l_)->nth(m, default0);
              }},
          this->v());
    }
  }
};

struct FetchOps {
  struct state {
    std::shared_ptr<List<unsigned int>> rom;
  };

  static unsigned int fetch_byte(const std::shared_ptr<state> &s,
                                 const unsigned int addr);
  static inline const unsigned int fetch_default_test =
      fetch_byte(std::make_shared<state>(state{List<unsigned int>::ctor::cons_(
                     1u, List<unsigned int>::ctor::cons_(
                             2u, List<unsigned int>::ctor::nil_()))}),
                 5u);
  static unsigned int
  fetch_byte_direct(const std::shared_ptr<List<unsigned int>> &rom_data,
                    const unsigned int addr);
  static inline const unsigned int fetch_in_range_test = fetch_byte_direct(
      List<unsigned int>::ctor::cons_(
          11u, List<unsigned int>::ctor::cons_(
                   22u, List<unsigned int>::ctor::cons_(
                            33u, List<unsigned int>::ctor::nil_()))),
      1u);

  template <typename T1>
  static std::shared_ptr<List<T1>> drop(const unsigned int n,
                                        std::shared_ptr<List<T1>> l) {
    if (n <= 0) {
      return std::move(l);
    } else {
      unsigned int n_ = n - 1;
      return std::visit(Overloaded{[](const typename List<T1>::nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::nil_();
                                   },
                                   [&](const typename List<T1>::cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     std::shared_ptr<List<T1>> l_ = _args._a1;
                                     return drop<T1>(std::move(n_),
                                                     std::move(l_));
                                   }},
                        l->v());
    }
  }

  static std::pair<unsigned int, unsigned int>
  fetch_pair(const std::shared_ptr<List<unsigned int>> &rom_data,
             const unsigned int addr);
  static inline const unsigned int fetch_pair_test = [](void) {
    std::pair<unsigned int, unsigned int> p =
        fetch_pair(List<unsigned int>::ctor::cons_(
                       1u, List<unsigned int>::ctor::cons_(
                               2u, List<unsigned int>::ctor::cons_(
                                       3u, List<unsigned int>::ctor::nil_()))),
                   0u);
    return (p.first + p.second);
  }();
  static std::optional<std::pair<unsigned int, unsigned int>>
  fetch_window(const std::shared_ptr<List<unsigned int>> &rom_data,
               const unsigned int addr);
  static inline const unsigned int fetch_window_test = [](void) {
    if (fetch_window(
            List<unsigned int>::ctor::cons_(
                9u, List<unsigned int>::ctor::cons_(
                        8u, List<unsigned int>::ctor::cons_(
                                7u, List<unsigned int>::ctor::nil_()))),
            0u)
            .has_value()) {
      std::pair<unsigned int, unsigned int> p = *fetch_window(
          List<unsigned int>::ctor::cons_(
              9u, List<unsigned int>::ctor::cons_(
                      8u, List<unsigned int>::ctor::cons_(
                              7u, List<unsigned int>::ctor::nil_()))),
          0u);
      unsigned int _x = p.first;
      unsigned int next = p.second;
      return std::move(next);
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
