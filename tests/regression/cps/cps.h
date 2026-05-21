#ifndef INCLUDED_CPS
#define INCLUDED_CPS

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_shared<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
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

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

struct Nat {
  static bool even(uint64_t n);
};

struct CPS {
  static uint64_t fact_cps(uint64_t n, std::function<uint64_t(uint64_t)> k) {
    if (n <= 0) {
      return k(UINT64_C(1));
    } else {
      uint64_t n_ = n - 1;
      return fact_cps(n_,
                      [=](uint64_t r) mutable { return k(((n_ + 1) * r)); });
    }
  }

  static uint64_t factorial(uint64_t n);

  static uint64_t fib_cps(uint64_t n, std::function<uint64_t(uint64_t)> k) {
    if (n <= 0) {
      return k(UINT64_C(0));
    } else {
      uint64_t n1 = n - 1;
      if (n1 <= 0) {
        return k(UINT64_C(1));
      } else {
        uint64_t n_ = n1 - 1;
        return fib_cps(n_, [=](uint64_t a) mutable {
          return fib_cps(n1, [=](uint64_t b) mutable { return k((a + b)); });
        });
      }
    }
  }

  static uint64_t fibonacci(uint64_t n);

  struct tree {
    // TYPES
    struct Leaf {
      uint64_t a0;
    };

    struct Node {
      std::shared_ptr<tree> a0;
      std::shared_ptr<tree> a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(std::move(_v)) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    tree(const tree &_other) : v_(std::move(_other.clone().v_)) {}

    tree(tree &&_other) noexcept : v_(std::move(_other.v_)) {}

    tree &operator=(const tree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    tree &operator=(tree &&_other) noexcept {
      v_ = std::move(_other.v_);
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
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          const auto &_alt = std::get<Leaf>(_src->v());
          _dst->v_ = Leaf{_alt.a0};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ = Node{_alt.a0 ? std::make_shared<tree>() : nullptr,
                          _alt.a1 ? std::make_shared<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf(uint64_t a0) { return tree(Leaf{a0}); }

    static tree node(tree a0, tree a1) {
      return tree(Node{std::make_shared<tree>(std::move(a0)),
                       std::make_shared<tree>(std::move(a1))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::shared_ptr<tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
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

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, tree &, T1 &, tree &, T1 &>
  static T1 tree_rect(F0 &&f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename tree::Leaf>(t.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rect<T1>(f, f0, *a0), *a1, tree_rect<T1>(f, f0, *a1));
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, tree &, T1 &, tree &, T1 &>
  static T1 tree_rec(F0 &&f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename tree::Leaf>(t.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rec<T1>(f, f0, *a0), *a1, tree_rec<T1>(f, f0, *a1));
    }
  }

  static uint64_t tree_sum_cps(const tree &t,
                               std::function<uint64_t(uint64_t)> k) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename tree::Leaf>(t.v());
      return k(a0);
    } else {
      const auto &[a0, a1] = std::get<typename tree::Node>(t.v());
      const tree &a0_value = *a0;
      const tree &a1_value = *a1;
      return tree_sum_cps(a0_value, [=](uint64_t sl) mutable {
        return tree_sum_cps(a1_value,
                            [=](uint64_t sr) mutable { return k((sl + sr)); });
      });
    }
  }

  static uint64_t tree_sum(const tree &t);

  static uint64_t sum_cps(const List<uint64_t> &l,
                          std::function<uint64_t(uint64_t)> k) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return k(UINT64_C(0));
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      const List<uint64_t> &a1_value = *a1;
      return sum_cps(a1_value, [=](uint64_t r) mutable { return k((a0 + r)); });
    }
  }

  static uint64_t list_sum(const List<uint64_t> &l);

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static uint64_t
  partition_cps(F0 &&p, const List<uint64_t> &l,
                std::function<uint64_t(List<uint64_t>, List<uint64_t>)> k) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return k(List<uint64_t>::nil(), List<uint64_t>::nil());
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      const List<uint64_t> &a1_value = *a1;
      return partition_cps(p, a1_value,
                           [=](List<uint64_t> yes, List<uint64_t> no) mutable {
                             if (p(a0)) {
                               return k(List<uint64_t>::cons(a0, yes), no);
                             } else {
                               return k(yes, List<uint64_t>::cons(a0, no));
                             }
                           });
    }
  }

  static uint64_t count_evens(const List<uint64_t> &l);
  static inline const uint64_t test_fact_5 = factorial(UINT64_C(5));
  static inline const uint64_t test_fib_7 = fibonacci(UINT64_C(7));
  static inline const uint64_t test_tree = tree_sum(
      tree::node(tree::node(tree::leaf(UINT64_C(1)), tree::leaf(UINT64_C(2))),
                 tree::leaf(UINT64_C(3))));
  static inline const uint64_t test_list_sum = list_sum(List<uint64_t>::cons(
      UINT64_C(10),
      List<uint64_t>::cons(
          UINT64_C(20),
          List<uint64_t>::cons(UINT64_C(30), List<uint64_t>::nil()))));
  static inline const uint64_t test_evens = count_evens(List<uint64_t>::cons(
      UINT64_C(1),
      List<uint64_t>::cons(
          UINT64_C(2),
          List<uint64_t>::cons(
              UINT64_C(3),
              List<uint64_t>::cons(
                  UINT64_C(4),
                  List<uint64_t>::cons(
                      UINT64_C(5),
                      List<uint64_t>::cons(UINT64_C(6),
                                           List<uint64_t>::nil())))))));
};

#endif // INCLUDED_CPS
