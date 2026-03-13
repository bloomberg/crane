#ifndef INCLUDED_FETCH_OPS
#define INCLUDED_FETCH_OPS

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

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  t_A nth(const unsigned int n, const t_A default0) const {
    if (n <= 0) {
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args) -> t_A {
                       return default0;
                     },
                     [](const typename List<t_A>::Cons _args) -> t_A {
                       t_A x = _args.d_a0;
                       return x;
                     }},
          this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args) -> t_A {
                       return default0;
                     },
                     [&](const typename List<t_A>::Cons _args) -> t_A {
                       std::shared_ptr<List<t_A>> l_ = _args.d_a1;
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

  __attribute__((pure)) static unsigned int
  fetch_byte(const std::shared_ptr<state> &s, const unsigned int addr);
  static inline const unsigned int fetch_default_test =
      fetch_byte(std::make_shared<state>(state{List<unsigned int>::ctor::Cons_(
                     1u, List<unsigned int>::ctor::Cons_(
                             2u, List<unsigned int>::ctor::Nil_()))}),
                 5u);
  __attribute__((pure)) static unsigned int
  fetch_byte_direct(const std::shared_ptr<List<unsigned int>> &rom_data,
                    const unsigned int addr);
  static inline const unsigned int fetch_in_range_test = fetch_byte_direct(
      List<unsigned int>::ctor::Cons_(
          11u, List<unsigned int>::ctor::Cons_(
                   22u, List<unsigned int>::ctor::Cons_(
                            33u, List<unsigned int>::ctor::Nil_()))),
      1u);

  template <typename T1>
  static std::shared_ptr<List<T1>> drop(const unsigned int n,
                                        std::shared_ptr<List<T1>> l) {
    if (n <= 0) {
      return std::move(l);
    } else {
      unsigned int n_ = n - 1;
      return std::visit(Overloaded{[](const typename List<T1>::Nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::Nil_();
                                   },
                                   [&](const typename List<T1>::Cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     std::shared_ptr<List<T1>> l_ = _args.d_a1;
                                     return drop<T1>(std::move(n_),
                                                     std::move(l_));
                                   }},
                        l->v());
    }
  }

  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  fetch_pair(const std::shared_ptr<List<unsigned int>> &rom_data,
             const unsigned int addr);
  static inline const unsigned int fetch_pair_test = [](void) {
    std::pair<unsigned int, unsigned int> p =
        fetch_pair(List<unsigned int>::ctor::Cons_(
                       1u, List<unsigned int>::ctor::Cons_(
                               2u, List<unsigned int>::ctor::Cons_(
                                       3u, List<unsigned int>::ctor::Nil_()))),
                   0u);
    return (p.first + p.second);
  }();
  __attribute__((
      pure)) static std::optional<std::pair<unsigned int, unsigned int>>
  fetch_window(const std::shared_ptr<List<unsigned int>> &rom_data,
               const unsigned int addr);
  static inline const unsigned int fetch_window_test = [](void) {
    if (fetch_window(
            List<unsigned int>::ctor::Cons_(
                9u, List<unsigned int>::ctor::Cons_(
                        8u, List<unsigned int>::ctor::Cons_(
                                7u, List<unsigned int>::ctor::Nil_()))),
            0u)
            .has_value()) {
      std::pair<unsigned int, unsigned int> p = *fetch_window(
          List<unsigned int>::ctor::Cons_(
              9u, List<unsigned int>::ctor::Cons_(
                      8u, List<unsigned int>::ctor::Cons_(
                              7u, List<unsigned int>::ctor::Nil_()))),
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

#endif // INCLUDED_FETCH_OPS
