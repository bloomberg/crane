#ifndef INCLUDED_LET_FIX
#define INCLUDED_LET_FIX

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
};

struct LetFix {
  static unsigned int local_sum(const std::shared_ptr<List<unsigned int>> &l);

  template <typename T1>
  static std::shared_ptr<List<T1>>
  local_rev(const std::shared_ptr<List<T1>> &l) {
    std::function<std::shared_ptr<List<T1>>(std::shared_ptr<List<T1>>,
                                            std::shared_ptr<List<T1>>)>
        go;
    go = [&](std::shared_ptr<List<T1>> acc,
             std::shared_ptr<List<T1>> xs) -> std::shared_ptr<List<T1>> {
      return std::visit(
          Overloaded{
              [&](const typename List<T1>::nil _args)
                  -> std::shared_ptr<List<T1>> { return std::move(acc); },
              [&](const typename List<T1>::cons _args)
                  -> std::shared_ptr<List<T1>> {
                T1 x = _args._a0;
                std::shared_ptr<List<T1>> rest = _args._a1;
                return go(List<T1>::ctor::cons_(x, std::move(acc)),
                          std::move(rest));
              }},
          xs->v());
    };
    return go(List<T1>::ctor::nil_(), l);
  }

  static std::shared_ptr<List<unsigned int>> local_flatten(
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &xss);
  static bool local_mem(const unsigned int n,
                        const std::shared_ptr<List<unsigned int>> &l);

  template <typename T1>
  static unsigned int local_length(const std::shared_ptr<List<T1>> &xs) {
    return std::visit(
        Overloaded{[](const typename List<T1>::nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<T1>::cons _args) -> unsigned int {
                     std::shared_ptr<List<T1>> rest = _args._a1;
                     return (local_length<T1>(std::move(rest)) + 1);
                   }},
        xs->v());
  }

  static inline const unsigned int test_sum =
      local_sum(List<unsigned int>::ctor::cons_(
          1u,
          List<unsigned int>::ctor::cons_(
              2u,
              List<unsigned int>::ctor::cons_(
                  3u, List<unsigned int>::ctor::cons_(
                          4u, List<unsigned int>::ctor::cons_(
                                  5u, List<unsigned int>::ctor::nil_()))))));
  static inline const std::shared_ptr<List<unsigned int>> test_rev =
      local_rev<unsigned int>(List<unsigned int>::ctor::cons_(
          1u, List<unsigned int>::ctor::cons_(
                  2u, List<unsigned int>::ctor::cons_(
                          3u, List<unsigned int>::ctor::nil_()))));
  static inline const std::shared_ptr<List<unsigned int>> test_flatten =
      local_flatten(List<std::shared_ptr<List<unsigned int>>>::ctor::cons_(
          List<unsigned int>::ctor::cons_(
              1u, List<unsigned int>::ctor::cons_(
                      2u, List<unsigned int>::ctor::nil_())),
          List<std::shared_ptr<List<unsigned int>>>::ctor::cons_(
              List<unsigned int>::ctor::cons_(3u,
                                              List<unsigned int>::ctor::nil_()),
              List<std::shared_ptr<List<unsigned int>>>::ctor::cons_(
                  List<unsigned int>::ctor::cons_(
                      4u, List<unsigned int>::ctor::cons_(
                              5u, List<unsigned int>::ctor::cons_(
                                      6u, List<unsigned int>::ctor::nil_()))),
                  List<std::shared_ptr<List<unsigned int>>>::ctor::nil_()))));
  static inline const bool test_mem_found = local_mem(
      3u, List<unsigned int>::ctor::cons_(
              1u, List<unsigned int>::ctor::cons_(
                      2u, List<unsigned int>::ctor::cons_(
                              3u, List<unsigned int>::ctor::cons_(
                                      4u, List<unsigned int>::ctor::nil_())))));
  static inline const bool test_mem_missing = local_mem(
      9u, List<unsigned int>::ctor::cons_(
              1u, List<unsigned int>::ctor::cons_(
                      2u, List<unsigned int>::ctor::cons_(
                              3u, List<unsigned int>::ctor::cons_(
                                      4u, List<unsigned int>::ctor::nil_())))));
  static inline const unsigned int test_length =
      local_length<unsigned int>(List<unsigned int>::ctor::cons_(
          10u, List<unsigned int>::ctor::cons_(
                   20u, List<unsigned int>::ctor::cons_(
                            30u, List<unsigned int>::ctor::cons_(
                                     40u, List<unsigned int>::ctor::nil_())))));
};

#endif // INCLUDED_LET_FIX
