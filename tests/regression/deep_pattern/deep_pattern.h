#ifndef INCLUDED_DEEP_PATTERN
#define INCLUDED_DEEP_PATTERN

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

struct DeepPattern {
  struct tree {
    // TYPES
    struct Leaf {
      unsigned int d_a0;
    };

    struct Node {
      std::shared_ptr<tree> d_a0;
      std::shared_ptr<tree> d_a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<tree> Leaf_(unsigned int a0) {
        return std::shared_ptr<tree>(new tree(Leaf{a0}));
      }

      static std::shared_ptr<tree> Node_(const std::shared_ptr<tree> &a0,
                                         const std::shared_ptr<tree> &a1) {
        return std::shared_ptr<tree>(new tree(Node{a0, a1}));
      }

      static std::unique_ptr<tree> Leaf_uptr(unsigned int a0) {
        return std::unique_ptr<tree>(new tree(Leaf{a0}));
      }

      static std::unique_ptr<tree> Node_uptr(const std::shared_ptr<tree> &a0,
                                             const std::shared_ptr<tree> &a1) {
        return std::unique_ptr<tree>(new tree(Node{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<tree>, T1, std::shared_ptr<tree>, T1> F1>
  static T1 tree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<tree> &t) {
    return std::visit(Overloaded{[&](const typename tree::Leaf _args) -> T1 {
                                   unsigned int n = _args.d_a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename tree::Node _args) -> T1 {
                                   std::shared_ptr<tree> t0 = _args.d_a0;
                                   std::shared_ptr<tree> t1 = _args.d_a1;
                                   return f0(t0, tree_rect<T1>(f, f0, t0), t1,
                                             tree_rect<T1>(f, f0, t1));
                                 }},
                      t->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<tree>, T1, std::shared_ptr<tree>, T1> F1>
  static T1 tree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<tree> &t) {
    return std::visit(Overloaded{[&](const typename tree::Leaf _args) -> T1 {
                                   unsigned int n = _args.d_a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename tree::Node _args) -> T1 {
                                   std::shared_ptr<tree> t0 = _args.d_a0;
                                   std::shared_ptr<tree> t1 = _args.d_a1;
                                   return f0(t0, tree_rec<T1>(f, f0, t0), t1,
                                             tree_rec<T1>(f, f0, t1));
                                 }},
                      t->v());
  }

  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::shared_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit list(Nil _v) : d_v_(std::move(_v)) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<list<t_A>> Nil_() {
        return std::shared_ptr<list<t_A>>(new list<t_A>(Nil{}));
      }

      static std::shared_ptr<list<t_A>>
      Cons_(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
        return std::shared_ptr<list<t_A>>(new list<t_A>(Cons{a0, a1}));
      }

      static std::unique_ptr<list<t_A>> Nil_uptr() {
        return std::unique_ptr<list<t_A>>(new list<t_A>(Nil{}));
      }

      static std::unique_ptr<list<t_A>>
      Cons_uptr(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
        return std::unique_ptr<list<t_A>>(new list<t_A>(Cons{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::Nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::Cons _args) -> T2 {
                     T1 y = _args.d_a0;
                     std::shared_ptr<list<T1>> l0 = _args.d_a1;
                     return f0(y, l0, list_rect<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::Nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::Cons _args) -> T2 {
                     T1 y = _args.d_a0;
                     std::shared_ptr<list<T1>> l0 = _args.d_a1;
                     return f0(y, l0, list_rec<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  __attribute__((pure)) static unsigned int
  deep_match(const std::shared_ptr<tree> &t);
  __attribute__((pure)) static unsigned int
  multi_constructor(const std::shared_ptr<tree> &t1,
                    const std::shared_ptr<tree> &t2);
  __attribute__((pure)) static unsigned int
  list_deep_match(const std::shared_ptr<list<std::shared_ptr<tree>>> &l);
  __attribute__((pure)) static unsigned int
  wildcard_with_bindings(const std::shared_ptr<tree> &t);
  static std::shared_ptr<tree> as_pattern_test(std::shared_ptr<tree> t);
  __attribute__((pure)) static bool has_value(const std::shared_ptr<tree> &t,
                                              const unsigned int target);
  __attribute__((pure)) static unsigned int
  conditional_match(const std::shared_ptr<tree> &t, const unsigned int target);
  __attribute__((pure)) static unsigned int
  nested_let_match(const std::shared_ptr<tree> &t);
  static inline const unsigned int test1 = deep_match(
      tree::ctor::Node_(tree::ctor::Leaf_(1u), tree::ctor::Leaf_(2u)));
  static inline const unsigned int test2 =
      multi_constructor(tree::ctor::Leaf_(5u), tree::ctor::Leaf_(10u));
};

#endif // INCLUDED_DEEP_PATTERN
