#ifndef INCLUDED_CPS
#define INCLUDED_CPS

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }
};

struct Nat {
  __attribute__((pure)) static bool even(const unsigned int &n);
};

struct CPS {
  __attribute__((pure)) static unsigned int
  fact_cps(const unsigned int &n,
           const std::function<unsigned int(unsigned int)> k) {
    if (n <= 0) {
      return k(1u);
    } else {
      unsigned int n_ = n - 1;
      return fact_cps(
          n_, [=](const unsigned int &r) mutable { return k(((n_ + 1) * r)); });
    }
  }

  __attribute__((pure)) static unsigned int factorial(const unsigned int &n);

  __attribute__((pure)) static unsigned int
  fib_cps(const unsigned int &n,
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
          return fib_cps(
              n1, [=](const unsigned int &b) mutable { return k((a + b)); });
        });
      }
    }
  }

  __attribute__((pure)) static unsigned int fibonacci(const unsigned int &n);

  struct tree {
    // TYPES
    struct Leaf {
      unsigned int d_a0;
    };

    struct Node {
      std::unique_ptr<tree> d_a0;
      std::unique_ptr<tree> d_a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    tree(const tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) tree &operator=(const tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) tree &operator=(tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) tree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<Leaf>(_sv.v());
        return tree(Leaf{d_a0});
      } else {
        const auto &[d_a0, d_a1] = std::get<Node>(_sv.v());
        return tree(
            Node{d_a0 ? std::make_unique<CPS::tree>(d_a0->clone()) : nullptr,
                 d_a1 ? std::make_unique<CPS::tree>(d_a1->clone()) : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree leaf(unsigned int a0) {
      return tree(Leaf{std::move(a0)});
    }

    __attribute__((pure)) static tree node(const tree &a0, const tree &a1) {
      return tree(Node{std::make_unique<tree>(a0), std::make_unique<tree>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) tree *operator->() { return this; }

    __attribute__((pure)) const tree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = tree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, tree, T1, tree, T1> F1>
  static T1 tree_rect(F0 &&f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      const auto &[d_a0] = std::get<typename tree::Leaf>(t.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rect<T1>(f, f0, *(d_a0)), *(d_a1),
                tree_rect<T1>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, tree, T1, tree, T1> F1>
  static T1 tree_rec(F0 &&f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      const auto &[d_a0] = std::get<typename tree::Leaf>(t.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rec<T1>(f, f0, *(d_a0)), *(d_a1),
                tree_rec<T1>(f, f0, *(d_a1)));
    }
  }

  __attribute__((pure)) static unsigned int
  tree_sum_cps(const tree &t,
               const std::function<unsigned int(unsigned int)> k) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      const auto &[d_a0] = std::get<typename tree::Leaf>(t.v());
      return k(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t.v());
      tree d_a0_value = *(d_a0);
      tree d_a1_value = *(d_a1);
      return tree_sum_cps(d_a0_value, [=](unsigned int sl) mutable {
        return tree_sum_cps(d_a1_value, [=](const unsigned int &sr) mutable {
          return k((sl + sr));
        });
      });
    }
  }

  __attribute__((pure)) static unsigned int tree_sum(const tree &t);

  __attribute__((pure)) static unsigned int
  sum_cps(const List<unsigned int> &l,
          const std::function<unsigned int(unsigned int)> k) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return k(0u);
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      List<unsigned int> d_a1_value = List<unsigned int>(*(d_a1));
      return sum_cps(d_a1_value, [=](const unsigned int &r) mutable {
        return k((d_a0 + r));
      });
    }
  }

  __attribute__((pure)) static unsigned int
  list_sum(const List<unsigned int> &l);

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static unsigned int partition_cps(
      F0 &&p, const List<unsigned int> &l,
      const std::function<unsigned int(List<unsigned int>, List<unsigned int>)>
          k) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return k(List<unsigned int>::nil(), List<unsigned int>::nil());
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      List<unsigned int> d_a1_value = List<unsigned int>(*(d_a1));
      return partition_cps(
          p, d_a1_value,
          [=](List<unsigned int> yes, List<unsigned int> no) mutable {
            if (p(d_a0)) {
              return k(List<unsigned int>::cons(d_a0, yes), no);
            } else {
              return k(yes, List<unsigned int>::cons(d_a0, no));
            }
          });
    }
  }

  __attribute__((pure)) static unsigned int
  count_evens(const List<unsigned int> &l);
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
