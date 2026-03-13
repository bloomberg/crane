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
};

struct LetFix {
  __attribute__((pure)) static unsigned int
  local_sum(const std::shared_ptr<List<unsigned int>> &l);

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
              [&](const typename List<T1>::Nil _args)
                  -> std::shared_ptr<List<T1>> { return std::move(acc); },
              [&](const typename List<T1>::Cons _args)
                  -> std::shared_ptr<List<T1>> {
                T1 x = _args.d_a0;
                std::shared_ptr<List<T1>> rest = _args.d_a1;
                return go(List<T1>::ctor::Cons_(x, std::move(acc)),
                          std::move(rest));
              }},
          xs->v());
    };
    return go(List<T1>::ctor::Nil_(), l);
  }

  static std::shared_ptr<List<unsigned int>> local_flatten(
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &xss);
  __attribute__((pure)) static bool
  local_mem(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);

  template <typename T1>
  __attribute__((pure)) static unsigned int
  local_length(const std::shared_ptr<List<T1>> &xs) {
    return std::visit(
        Overloaded{[](const typename List<T1>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<T1>::Cons _args) -> unsigned int {
                     std::shared_ptr<List<T1>> rest = _args.d_a1;
                     return (local_length<T1>(std::move(rest)) + 1);
                   }},
        xs->v());
  }

  static inline const unsigned int test_sum =
      local_sum(List<unsigned int>::ctor::Cons_(
          1u,
          List<unsigned int>::ctor::Cons_(
              2u,
              List<unsigned int>::ctor::Cons_(
                  3u, List<unsigned int>::ctor::Cons_(
                          4u, List<unsigned int>::ctor::Cons_(
                                  5u, List<unsigned int>::ctor::Nil_()))))));
  static inline const std::shared_ptr<List<unsigned int>> test_rev =
      local_rev<unsigned int>(List<unsigned int>::ctor::Cons_(
          1u, List<unsigned int>::ctor::Cons_(
                  2u, List<unsigned int>::ctor::Cons_(
                          3u, List<unsigned int>::ctor::Nil_()))));
  static inline const std::shared_ptr<List<unsigned int>> test_flatten =
      local_flatten(List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
          List<unsigned int>::ctor::Cons_(
              1u, List<unsigned int>::ctor::Cons_(
                      2u, List<unsigned int>::ctor::Nil_())),
          List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
              List<unsigned int>::ctor::Cons_(3u,
                                              List<unsigned int>::ctor::Nil_()),
              List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                  List<unsigned int>::ctor::Cons_(
                      4u, List<unsigned int>::ctor::Cons_(
                              5u, List<unsigned int>::ctor::Cons_(
                                      6u, List<unsigned int>::ctor::Nil_()))),
                  List<std::shared_ptr<List<unsigned int>>>::ctor::Nil_()))));
  static inline const bool test_mem_found = local_mem(
      3u, List<unsigned int>::ctor::Cons_(
              1u, List<unsigned int>::ctor::Cons_(
                      2u, List<unsigned int>::ctor::Cons_(
                              3u, List<unsigned int>::ctor::Cons_(
                                      4u, List<unsigned int>::ctor::Nil_())))));
  static inline const bool test_mem_missing = local_mem(
      9u, List<unsigned int>::ctor::Cons_(
              1u, List<unsigned int>::ctor::Cons_(
                      2u, List<unsigned int>::ctor::Cons_(
                              3u, List<unsigned int>::ctor::Cons_(
                                      4u, List<unsigned int>::ctor::Nil_())))));
  static inline const unsigned int test_length =
      local_length<unsigned int>(List<unsigned int>::ctor::Cons_(
          10u, List<unsigned int>::ctor::Cons_(
                   20u, List<unsigned int>::ctor::Cons_(
                            30u, List<unsigned int>::ctor::Cons_(
                                     40u, List<unsigned int>::ctor::Nil_())))));
};

#endif // INCLUDED_LET_FIX
