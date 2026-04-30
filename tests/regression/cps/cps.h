#ifndef INCLUDED_CPS
#define INCLUDED_CPS

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
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

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }

  unsigned int length() const {
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
  static bool even(const unsigned int &n);
};

struct CPS {
  static unsigned int
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

  static unsigned int factorial(const unsigned int &n);

  static unsigned int
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

  static unsigned int fibonacci(const unsigned int &n);

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

    tree &operator=(const tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tree &operator=(tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    tree clone() const {
      tree _out{};

      struct _CloneFrame {
        const tree *_src;
        tree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          const auto &_alt = std::get<Leaf>(_src->v());
          _dst->d_v_ = Leaf{_alt.d_a0};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ = Node{_alt.d_a0 ? std::make_unique<tree>() : nullptr,
                            _alt.d_a1 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf(unsigned int a0) { return tree(Leaf{std::move(a0)}); }

    static tree node(tree a0, tree a1) {
      return tree(Node{std::make_unique<tree>(std::move(a0)),
                       std::make_unique<tree>(std::move(a1))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.d_v_)) {
          auto &_alt = std::get<Node>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
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

  static unsigned int
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

  static unsigned int tree_sum(const tree &t);

  static unsigned int
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

  static unsigned int list_sum(const List<unsigned int> &l);

  template <MapsTo<bool, unsigned int> F0>
  static unsigned int partition_cps(
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

  static unsigned int count_evens(const List<unsigned int> &l);
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
