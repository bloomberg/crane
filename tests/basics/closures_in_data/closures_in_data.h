#ifndef INCLUDED_CLOSURES_IN_DATA
#define INCLUDED_CLOSURES_IN_DATA

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

  template <typename T1, MapsTo<T1, T1, A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    return std::visit(
        Overloaded{[&](const typename List<A>::nil _args) -> T1 { return a0; },
                   [&](const typename List<A>::cons _args) -> T1 {
                     A b = _args._a0;
                     std::shared_ptr<List<A>> l0 = _args._a1;
                     return std::move(l0)->template fold_left<T1>(f, f(a0, b));
                   }},
        this->v());
  }

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
};

struct Nat {
  static std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                                      const unsigned int y,
                                                      const unsigned int q,
                                                      const unsigned int u);
  static unsigned int div(const unsigned int x, const unsigned int y);
};

struct ClosuresInData {
  static inline const std::shared_ptr<
      List<std::function<unsigned int(unsigned int)>>>
      fn_list = List<std::function<unsigned int(unsigned int)>>::ctor::cons_(
          [](unsigned int x) { return (x + 1); },
          List<std::function<unsigned int(unsigned int)>>::ctor::cons_(
              [](unsigned int x) { return (x + x); },
              List<std::function<unsigned int(unsigned int)>>::ctor::cons_(
                  [](unsigned int x) { return (x * x); },
                  List<std::function<unsigned int(unsigned int)>>::ctor::
                      nil_())));
  static std::shared_ptr<List<unsigned int>> apply_all(
      const std::shared_ptr<List<std::function<unsigned int(unsigned int)>>>
          &fns,
      const unsigned int x);

  struct transform {
    std::function<unsigned int(unsigned int)> forward;
    std::function<unsigned int(unsigned int)> backward;
  };

  static inline const std::shared_ptr<transform> double_transform =
      std::make_shared<transform>(
          transform{[](unsigned int x) { return (x + x); },
                    [](unsigned int x) { return Nat::div(x, 2u); }});
  static unsigned int apply_forward(const std::shared_ptr<transform> &t,
                                    const unsigned int x);
  static unsigned int apply_backward(const std::shared_ptr<transform> &t,
                                     const unsigned int x);
  static unsigned int compose_all(
      const std::shared_ptr<List<std::function<unsigned int(unsigned int)>>>
          &fns,
      const unsigned int x);
  static inline const std::shared_ptr<
      List<std::function<unsigned int(unsigned int)>>>
      pipeline = List<std::function<unsigned int(unsigned int)>>::ctor::cons_(
          [](unsigned int x) { return (x + 1u); },
          List<std::function<unsigned int(unsigned int)>>::ctor::cons_(
              [](unsigned int x) { return (x * 2u); },
              List<std::function<unsigned int(unsigned int)>>::ctor::cons_(
                  [](unsigned int x) { return (x + 10u); },
                  List<std::function<unsigned int(unsigned int)>>::ctor::
                      nil_())));
  static unsigned int
  maybe_apply(const std::optional<std::function<unsigned int(unsigned int)>> mf,
              const unsigned int x);
  static inline const std::shared_ptr<List<unsigned int>> test_apply_all =
      apply_all(fn_list, 5u);
  static inline const unsigned int test_forward =
      apply_forward(double_transform, 7u);
  static inline const unsigned int test_backward =
      apply_backward(double_transform, 14u);
  static inline const unsigned int test_compose = compose_all(pipeline, 3u);
  static inline const unsigned int test_maybe_some =
      maybe_apply(std::make_optional<std::function<unsigned int(unsigned int)>>(
                      [](unsigned int x) { return (x + 1); }),
                  41u);
  static inline const unsigned int test_maybe_none =
      maybe_apply(std::nullopt, 42u);
};

#endif // INCLUDED_CLOSURES_IN_DATA
