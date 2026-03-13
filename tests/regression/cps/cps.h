#ifndef INCLUDED_CPS
#define INCLUDED_CPS

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
};

struct Nat {
  __attribute__((pure)) static bool even(const unsigned int n);
};

struct CPS {
  __attribute__((pure)) static unsigned int
  fact_cps(const unsigned int n,
           const std::function<unsigned int(unsigned int)> k) {
    if (n <= 0) {
      return k(1u);
    } else {
      unsigned int n_ = n - 1;
      return fact_cps(
          n_, [=](unsigned int r) mutable { return k(((n_ + 1) * r)); });
    }
  }

  __attribute__((pure)) static unsigned int factorial(const unsigned int n);

  __attribute__((pure)) static unsigned int
  fib_cps(const unsigned int n,
          const std::function<unsigned int(unsigned int)> k) {
    if (n <= 0) {
      return k(0u);
    } else {
      unsigned int n1 = n - 1;
      if (n1 <= 0) {
        return k(1u);
      } else {
        unsigned int n_ = n1 - 1;
        return fib_cps(n_, [=](unsigned int a) mutable {
          return fib_cps(n1,
                         [=](unsigned int b) mutable { return k((a + b)); });
        });
      }
    }
  }

  __attribute__((pure)) static unsigned int fibonacci(const unsigned int n);

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

  __attribute__((pure)) static unsigned int
  tree_sum_cps(const std::shared_ptr<tree> &t,
               const std::function<unsigned int(unsigned int)> k) {
    return std::visit(
        Overloaded{[&](const typename tree::Leaf _args) -> unsigned int {
                     unsigned int n = _args.d_a0;
                     return k(std::move(n));
                   },
                   [&](const typename tree::Node _args) -> unsigned int {
                     std::shared_ptr<tree> l = _args.d_a0;
                     std::shared_ptr<tree> r = _args.d_a1;
                     return tree_sum_cps(
                         std::move(l), [=](unsigned int sl) mutable {
                           return tree_sum_cps(r, [=](unsigned int sr) mutable {
                             return k((sl + sr));
                           });
                         });
                   }},
        t->v());
  }

  __attribute__((pure)) static unsigned int
  tree_sum(const std::shared_ptr<tree> &t);

  __attribute__((pure)) static unsigned int
  sum_cps(const std::shared_ptr<List<unsigned int>> &l,
          const std::function<unsigned int(unsigned int)> k) {
    return std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) -> unsigned int {
              return k(0u);
            },
            [&](const typename List<unsigned int>::Cons _args) -> unsigned int {
              unsigned int x = _args.d_a0;
              std::shared_ptr<List<unsigned int>> rest = _args.d_a1;
              return sum_cps(std::move(rest), [=](unsigned int r) mutable {
                return k((x + r));
              });
            }},
        l->v());
  }

  __attribute__((pure)) static unsigned int
  list_sum(const std::shared_ptr<List<unsigned int>> &l);

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static unsigned int partition_cps(
      F0 &&p, const std::shared_ptr<List<unsigned int>> &l,
      const std::function<unsigned int(std::shared_ptr<List<unsigned int>>,
                                       std::shared_ptr<List<unsigned int>>)>
          k) {
    return std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) -> unsigned int {
              return k(List<unsigned int>::ctor::Nil_(),
                       List<unsigned int>::ctor::Nil_());
            },
            [&](const typename List<unsigned int>::Cons _args) -> unsigned int {
              unsigned int x = _args.d_a0;
              std::shared_ptr<List<unsigned int>> rest = _args.d_a1;
              return partition_cps(
                  p, std::move(rest),
                  [=](std::shared_ptr<List<unsigned int>> yes,
                      std::shared_ptr<List<unsigned int>> no) mutable {
                    if (p(x)) {
                      return k(List<unsigned int>::ctor::Cons_(x, yes), no);
                    } else {
                      return k(yes, List<unsigned int>::ctor::Cons_(x, no));
                    }
                  });
            }},
        l->v());
  }

  __attribute__((pure)) static unsigned int
  count_evens(const std::shared_ptr<List<unsigned int>> &l);
  static inline const unsigned int test_fact_5 = factorial(5u);
  static inline const unsigned int test_fib_7 = fibonacci(7u);
  static inline const unsigned int test_tree = tree_sum(tree::ctor::Node_(
      tree::ctor::Node_(tree::ctor::Leaf_(1u), tree::ctor::Leaf_(2u)),
      tree::ctor::Leaf_(3u)));
  static inline const unsigned int test_list_sum =
      list_sum(List<unsigned int>::ctor::Cons_(
          10u, List<unsigned int>::ctor::Cons_(
                   20u, List<unsigned int>::ctor::Cons_(
                            30u, List<unsigned int>::ctor::Nil_()))));
  static inline const unsigned int test_evens =
      count_evens(List<unsigned int>::ctor::Cons_(
          1u,
          List<unsigned int>::ctor::Cons_(
              2u,
              List<unsigned int>::ctor::Cons_(
                  3u,
                  List<unsigned int>::ctor::Cons_(
                      4u,
                      List<unsigned int>::ctor::Cons_(
                          5u, List<unsigned int>::ctor::Cons_(
                                  6u, List<unsigned int>::ctor::Nil_())))))));
};

#endif // INCLUDED_CPS
