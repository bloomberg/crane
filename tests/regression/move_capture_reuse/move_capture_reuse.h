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

  template <typename T1, MapsTo<T1, A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> std::shared_ptr<List<T1>> {
              return List<T1>::ctor::nil_();
            },
            [&](const typename List<A>::cons _args)
                -> std::shared_ptr<List<T1>> {
              A a = _args._a0;
              std::shared_ptr<List<A>> l0 = _args._a1;
              return List<T1>::ctor::cons_(f(a),
                                           std::move(l0)->template map<T1>(f));
            }},
        this->v());
  }

  unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<A>::nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<A>::cons _args) -> unsigned int {
                     std::shared_ptr<List<A>> l_ = _args._a1;
                     return (std::move(l_)->length() + 1);
                   }},
        this->v());
  }

  std::shared_ptr<List<A>> app(std::shared_ptr<List<A>> m) const {
    return std::visit(Overloaded{[&](const typename List<A>::nil _args)
                                     -> std::shared_ptr<List<A>> { return m; },
                                 [&](const typename List<A>::cons _args)
                                     -> std::shared_ptr<List<A>> {
                                   A a = _args._a0;
                                   std::shared_ptr<List<A>> l1 = _args._a1;
                                   return List<A>::ctor::cons_(
                                       a, std::move(l1)->app(m));
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
          List<unsigned int>::ctor::cons_(1u, List<unsigned int>::ctor::nil_()),
          List<std::shared_ptr<List<unsigned int>>>::ctor::cons_(
              List<unsigned int>::ctor::cons_(10u,
                                              List<unsigned int>::ctor::nil_()),
              List<std::shared_ptr<List<unsigned int>>>::ctor::cons_(
                  List<unsigned int>::ctor::cons_(
                      20u, List<unsigned int>::ctor::nil_()),
                  List<std::shared_ptr<List<unsigned int>>>::ctor::nil_())));
  static inline const unsigned int len_sum = []() {
    return std::visit(
        Overloaded{
            [](const typename List<std::shared_ptr<List<unsigned int>>>::nil
                   _args) -> unsigned int { return 0u; },
            [](const typename List<std::shared_ptr<List<unsigned int>>>::cons
                   _args) -> unsigned int {
              std::shared_ptr<List<unsigned int>> a = _args._a0;
              std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> l =
                  _args._a1;
              return std::visit(
                  Overloaded{
                      [](const typename List<
                          std::shared_ptr<List<unsigned int>>>::nil _args)
                          -> unsigned int { return 0u; },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::cons _args)
                          -> unsigned int {
                        std::shared_ptr<List<unsigned int>> b = _args._a0;
                        return (std::move(a)->length() +
                                std::move(b)->length());
                      }},
                  std::move(l)->v());
            }},
        sample->v());
  }();
};

#endif // INCLUDED_MOVE_CAPTURE_REUSE
