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
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
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
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
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
};

struct Nat {
  static bool even(const unsigned int n);
};

struct CPS {
  static unsigned int
  fact_cps(const unsigned int n,
           const std::function<unsigned int(unsigned int)> k) {
    if (n <= 0) {
      return k(1u);
    } else {
      unsigned int n_ = n - 1;
      return fact_cps(n_, [&](unsigned int r) { return k(((n_ + 1) * r)); });
    }
  }

  static unsigned int factorial(const unsigned int n);

  static unsigned int
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
        return fib_cps(n_, [&](unsigned int a) {
          return fib_cps(n1, [&](unsigned int b) { return k((a + b)); });
        });
      }
    }
  }

  static unsigned int fibonacci(const unsigned int n);

  struct tree {
  public:
    struct Leaf {
      unsigned int _a0;
    };
    struct Node {
      std::shared_ptr<tree> _a0;
      std::shared_ptr<tree> _a1;
    };
    using variant_t = std::variant<Leaf, Node>;

  private:
    variant_t v_;
    explicit tree(Leaf _v) : v_(std::move(_v)) {}
    explicit tree(Node _v) : v_(std::move(_v)) {}

  public:
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
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<tree>, T1, std::shared_ptr<tree>, T1> F1>
  static T1 tree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<tree> &t) {
    return std::visit(Overloaded{[&](const typename tree::Leaf _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename tree::Node _args) -> T1 {
                                   std::shared_ptr<tree> t0 = _args._a0;
                                   std::shared_ptr<tree> t1 = _args._a1;
                                   return f0(t0, tree_rect<T1>(f, f0, t0), t1,
                                             tree_rect<T1>(f, f0, t1));
                                 }},
                      t->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<tree>, T1, std::shared_ptr<tree>, T1> F1>
  static T1 tree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<tree> &t) {
    return std::visit(Overloaded{[&](const typename tree::Leaf _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename tree::Node _args) -> T1 {
                                   std::shared_ptr<tree> t0 = _args._a0;
                                   std::shared_ptr<tree> t1 = _args._a1;
                                   return f0(t0, tree_rec<T1>(f, f0, t0), t1,
                                             tree_rec<T1>(f, f0, t1));
                                 }},
                      t->v());
  }

  static unsigned int
  tree_sum_cps(const std::shared_ptr<tree> &t,
               const std::function<unsigned int(unsigned int)> k) {
    return std::visit(
        Overloaded{[&](const typename tree::Leaf _args) -> unsigned int {
                     unsigned int n = _args._a0;
                     return k(std::move(n));
                   },
                   [&](const typename tree::Node _args) -> unsigned int {
                     std::shared_ptr<tree> l = _args._a0;
                     std::shared_ptr<tree> r = _args._a1;
                     return tree_sum_cps(std::move(l), [&](unsigned int sl) {
                       return tree_sum_cps(
                           r, [&](unsigned int sr) { return k((sl + sr)); });
                     });
                   }},
        t->v());
  }

  static unsigned int tree_sum(const std::shared_ptr<tree> &t);

  static unsigned int
  sum_cps(const std::shared_ptr<List<unsigned int>> &l,
          const std::function<unsigned int(unsigned int)> k) {
    return std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::nil _args) -> unsigned int {
              return k(0u);
            },
            [&](const typename List<unsigned int>::cons _args) -> unsigned int {
              unsigned int x = _args._a0;
              std::shared_ptr<List<unsigned int>> rest = _args._a1;
              return sum_cps(std::move(rest),
                             [&](unsigned int r) { return k((x + r)); });
            }},
        l->v());
  }

  static unsigned int list_sum(const std::shared_ptr<List<unsigned int>> &l);

  template <MapsTo<bool, unsigned int> F0>
  static unsigned int partition_cps(
      F0 &&p, const std::shared_ptr<List<unsigned int>> &l,
      const std::function<unsigned int(std::shared_ptr<List<unsigned int>>,
                                       std::shared_ptr<List<unsigned int>>)>
          k) {
    return std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::nil _args) -> unsigned int {
              return k(List<unsigned int>::ctor::nil_(),
                       List<unsigned int>::ctor::nil_());
            },
            [&](const typename List<unsigned int>::cons _args) -> unsigned int {
              unsigned int x = _args._a0;
              std::shared_ptr<List<unsigned int>> rest = _args._a1;
              return partition_cps(
                  p, std::move(rest),
                  [&](std::shared_ptr<List<unsigned int>> yes,
                      std::shared_ptr<List<unsigned int>> no) {
                    if (p(x)) {
                      return k(List<unsigned int>::ctor::cons_(x, yes), no);
                    } else {
                      return k(yes, List<unsigned int>::ctor::cons_(x, no));
                    }
                  });
            }},
        l->v());
  }

  static unsigned int count_evens(const std::shared_ptr<List<unsigned int>> &l);

  static inline const unsigned int test_fact_5 = factorial(5u);

  static inline const unsigned int test_fib_7 = fibonacci(7u);

  static inline const unsigned int test_tree = tree_sum(tree::ctor::Node_(
      tree::ctor::Node_(tree::ctor::Leaf_(1u), tree::ctor::Leaf_(2u)),
      tree::ctor::Leaf_(3u)));

  static inline const unsigned int test_list_sum =
      list_sum(List<unsigned int>::ctor::cons_(
          10u, List<unsigned int>::ctor::cons_(
                   20u, List<unsigned int>::ctor::cons_(
                            30u, List<unsigned int>::ctor::nil_()))));

  static inline const unsigned int test_evens =
      count_evens(List<unsigned int>::ctor::cons_(
          1u,
          List<unsigned int>::ctor::cons_(
              2u,
              List<unsigned int>::ctor::cons_(
                  3u,
                  List<unsigned int>::ctor::cons_(
                      4u,
                      List<unsigned int>::ctor::cons_(
                          5u, List<unsigned int>::ctor::cons_(
                                  6u, List<unsigned int>::ctor::nil_())))))));
};
