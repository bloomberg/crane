#ifndef INCLUDED_UPDATE_NTH_BOUNDS
#define INCLUDED_UPDATE_NTH_BOUNDS

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A>
struct List : public std::enable_shared_from_this<List<t_A>> {
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

  std::shared_ptr<List<t_A>> skipn(const unsigned int n) const {
    if (n <= 0) {
      return std::const_pointer_cast<List<t_A>>(this->shared_from_this());
    } else {
      unsigned int n0 = n - 1;
      return std::visit(Overloaded{[](const typename List<t_A>::Nil _args)
                                       -> std::shared_ptr<List<t_A>> {
                                     return List<t_A>::ctor::Nil_();
                                   },
                                   [&](const typename List<t_A>::Cons _args)
                                       -> std::shared_ptr<List<t_A>> {
                                     std::shared_ptr<List<t_A>> l0 = _args.d_a1;
                                     return std::move(l0)->skipn(n0);
                                   }},
                        this->v());
    }
  }

  std::shared_ptr<List<t_A>> firstn(const unsigned int n) const {
    if (n <= 0) {
      return List<t_A>::ctor::Nil_();
    } else {
      unsigned int n0 = n - 1;
      return std::visit(Overloaded{[](const typename List<t_A>::Nil _args)
                                       -> std::shared_ptr<List<t_A>> {
                                     return List<t_A>::ctor::Nil_();
                                   },
                                   [&](const typename List<t_A>::Cons _args)
                                       -> std::shared_ptr<List<t_A>> {
                                     t_A a = _args.d_a0;
                                     std::shared_ptr<List<t_A>> l0 = _args.d_a1;
                                     return List<t_A>::ctor::Cons_(
                                         a, std::move(l0)->firstn(n0));
                                   }},
                        this->v());
    }
  }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons _args) -> unsigned int {
                     std::shared_ptr<List<t_A>> l_ = _args.d_a1;
                     return (std::move(l_)->length() + 1);
                   }},
        this->v());
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    return std::visit(
        Overloaded{[&](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<t_A>> { return m; },
                   [&](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<t_A>> {
                     t_A a = _args.d_a0;
                     std::shared_ptr<List<t_A>> l1 = _args.d_a1;
                     return List<t_A>::ctor::Cons_(a, std::move(l1)->app(m));
                   }},
        this->v());
  }
};

struct UpdateNthBounds {
  template <typename T1>
  static std::shared_ptr<List<T1>> update_nth(const unsigned int n, const T1 x,
                                              std::shared_ptr<List<T1>> l) {
    if (n < l->length()) {
      return l->firstn(n)->app(List<T1>::ctor::Cons_(x, l->skipn((n + 1))));
    } else {
      return std::move(l);
    }
  }

  static inline const unsigned int in_bounds_length =
      update_nth<unsigned int>(
          2u, 9u,
          List<unsigned int>::ctor::Cons_(
              1u, List<unsigned int>::ctor::Cons_(
                      2u, List<unsigned int>::ctor::Cons_(
                              3u, List<unsigned int>::ctor::Cons_(
                                      4u, List<unsigned int>::ctor::Nil_())))))
          ->length();
  static inline const unsigned int out_of_bounds_length =
      update_nth<unsigned int>(
          9u, 7u,
          List<unsigned int>::ctor::Cons_(
              1u, List<unsigned int>::ctor::Cons_(
                      2u, List<unsigned int>::ctor::Cons_(
                              3u, List<unsigned int>::ctor::Nil_()))))
          ->length();
};

#endif // INCLUDED_UPDATE_NTH_BOUNDS
