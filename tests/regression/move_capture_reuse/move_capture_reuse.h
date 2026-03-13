#ifndef INCLUDED_MOVE_CAPTURE_REUSE
#define INCLUDED_MOVE_CAPTURE_REUSE

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

  template <typename T1, MapsTo<T1, t_A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil _args)
                -> std::shared_ptr<List<T1>> { return List<T1>::ctor::Nil_(); },
            [&](const typename List<t_A>::Cons _args)
                -> std::shared_ptr<List<T1>> {
              t_A a = _args.d_a0;
              std::shared_ptr<List<t_A>> l0 = _args.d_a1;
              return List<T1>::ctor::Cons_(f(a),
                                           std::move(l0)->template map<T1>(f));
            }},
        this->v());
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

struct MoveCaptureReuse {
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> prefix_each(
      std::shared_ptr<List<unsigned int>> prefix,
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &xss);
  static inline const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
      sample = prefix_each(
          List<unsigned int>::ctor::Cons_(1u, List<unsigned int>::ctor::Nil_()),
          List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
              List<unsigned int>::ctor::Cons_(10u,
                                              List<unsigned int>::ctor::Nil_()),
              List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                  List<unsigned int>::ctor::Cons_(
                      20u, List<unsigned int>::ctor::Nil_()),
                  List<std::shared_ptr<List<unsigned int>>>::ctor::Nil_())));
  static inline const unsigned int len_sum = []() {
    return std::visit(
        Overloaded{
            [](const typename List<std::shared_ptr<List<unsigned int>>>::Nil
                   _args) -> unsigned int { return 0u; },
            [](const typename List<std::shared_ptr<List<unsigned int>>>::Cons
                   _args) -> unsigned int {
              std::shared_ptr<List<unsigned int>> a = _args.d_a0;
              std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> l =
                  _args.d_a1;
              return std::visit(
                  Overloaded{
                      [](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Nil _args)
                          -> unsigned int { return 0u; },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> unsigned int {
                        std::shared_ptr<List<unsigned int>> b = _args.d_a0;
                        return (std::move(a)->length() +
                                std::move(b)->length());
                      }},
                  std::move(l)->v());
            }},
        sample->v());
  }();
};

#endif // INCLUDED_MOVE_CAPTURE_REUSE
