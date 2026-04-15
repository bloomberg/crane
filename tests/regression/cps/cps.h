#ifndef INCLUDED_CPS
#define INCLUDED_CPS

#include <functional>
#include <memory>
#include <type_traits>
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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return (d_a1->length() + 1);
    }
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
          n_, [=](const unsigned int r) mutable { return k(((n_ + 1) * r)); });
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
        return fib_cps(n_, [=](const unsigned int a) mutable {
          return fib_cps(
              n1, [=](const unsigned int b) mutable { return k((a + b)); });
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

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree> leaf(unsigned int a0) {
      return std::make_shared<tree>(Leaf{std::move(a0)});
    }

    static std::shared_ptr<tree> node(const std::shared_ptr<tree> &a0,
                                      const std::shared_ptr<tree> &a1) {
      return std::make_shared<tree>(Node{a0, a1});
    }

    static std::shared_ptr<tree> node(std::shared_ptr<tree> &&a0,
                                      std::shared_ptr<tree> &&a1) {
      return std::make_shared<tree>(Node{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<tree>, T1, std::shared_ptr<tree>, T1> F1>
  static T1 tree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<tree> &t) {
    if (std::holds_alternative<typename tree::Leaf>(t->v())) {
      const auto &[d_a0] = std::get<typename tree::Leaf>(t->v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t->v());
      return f0(d_a0, tree_rect<T1>(f, f0, d_a0), d_a1,
                tree_rect<T1>(f, f0, d_a1));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<tree>, T1, std::shared_ptr<tree>, T1> F1>
  static T1 tree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<tree> &t) {
    if (std::holds_alternative<typename tree::Leaf>(t->v())) {
      const auto &[d_a0] = std::get<typename tree::Leaf>(t->v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t->v());
      return f0(d_a0, tree_rec<T1>(f, f0, d_a0), d_a1,
                tree_rec<T1>(f, f0, d_a1));
    }
  }

  __attribute__((pure)) static unsigned int
  tree_sum_cps(const std::shared_ptr<tree> &t,
               const std::function<unsigned int(unsigned int)> k) {
    if (std::holds_alternative<typename tree::Leaf>(t->v())) {
      const auto &[d_a0] = std::get<typename tree::Leaf>(t->v());
      return k(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t->v());
      return tree_sum_cps(d_a0, [=](const unsigned int sl) mutable {
        return tree_sum_cps(
            d_a1, [=](const unsigned int sr) mutable { return k((sl + sr)); });
      });
    }
  }

  __attribute__((pure)) static unsigned int
  tree_sum(const std::shared_ptr<tree> &t);

  __attribute__((pure)) static unsigned int
  sum_cps(const std::shared_ptr<List<unsigned int>> &l,
          const std::function<unsigned int(unsigned int)> k) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
      return k(0u);
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l->v());
      return sum_cps(
          d_a1, [=](const unsigned int r) mutable { return k((d_a0 + r)); });
    }
  }

  __attribute__((pure)) static unsigned int
  list_sum(const std::shared_ptr<List<unsigned int>> &l);

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static unsigned int partition_cps(
      F0 &&p, const std::shared_ptr<List<unsigned int>> &l,
      const std::function<unsigned int(std::shared_ptr<List<unsigned int>>,
                                       std::shared_ptr<List<unsigned int>>)>
          k) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
      return k(List<unsigned int>::nil(), List<unsigned int>::nil());
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l->v());
      return partition_cps(
          p, d_a1,
          [=](std::shared_ptr<List<unsigned int>> yes,
              std::shared_ptr<List<unsigned int>> no) mutable {
            if (p(d_a0)) {
              return k(List<unsigned int>::cons(d_a0, yes), no);
            } else {
              return k(yes, List<unsigned int>::cons(d_a0, no));
            }
          });
    }
  }

  __attribute__((pure)) static unsigned int
  count_evens(const std::shared_ptr<List<unsigned int>> &l);
  static inline const unsigned int test_fact_5 = factorial(5u);
  static inline const unsigned int test_fib_7 = fibonacci(7u);
  static inline const unsigned int test_tree = tree_sum(
      tree::node(tree::node(tree::leaf(1u), tree::leaf(2u)), tree::leaf(3u)));
  static inline const unsigned int test_list_sum =
      list_sum(List<unsigned int>::cons(
          10u,
          List<unsigned int>::cons(
              20u, List<unsigned int>::cons(30u, List<unsigned int>::nil()))));
  static inline const unsigned int test_evens =
      count_evens(List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u,
              List<unsigned int>::cons(
                  3u, List<unsigned int>::cons(
                          4u, List<unsigned int>::cons(
                                  5u, List<unsigned int>::cons(
                                          6u, List<unsigned int>::nil())))))));
};

#endif // INCLUDED_CPS
