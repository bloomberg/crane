#ifndef INCLUDED_BINOMIAL_HEAP
#define INCLUDED_BINOMIAL_HEAP

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
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
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
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
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
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

struct BinomialHeap {
  using key = unsigned int;

  struct tree {
    // TYPES
    struct Node {
      key a0;
      std::unique_ptr<tree> a1;
      std::unique_ptr<tree> a2;
    };

    struct Leaf {};

    using variant_t = std::variant<Node, Leaf>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    explicit tree(Leaf _v) : v_(_v) {}

    tree(const tree &_other) : v_(std::move(_other.clone().v_)) {}

    tree(tree &&_other) : v_(std::move(_other.v_)) {}

    tree &operator=(const tree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    tree &operator=(tree &&_other) {
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
        if (std::holds_alternative<Node>(_src->v())) {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ = Node{_alt.a0, _alt.a1 ? std::make_unique<tree>() : nullptr,
                          _alt.a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        } else {
          _dst->v_ = Leaf{};
        }
      }
      return _out;
    }

    // CREATORS
    static tree node(key a0, tree a1, tree a2) {
      return tree(Node{std::move(a0), std::make_unique<tree>(std::move(a1)),
                       std::make_unique<tree>(std::move(a2))});
    }

    static tree leaf() { return tree(Leaf{}); }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &, tree &, T1 &,
                                   tree &, T1 &>
  static T1 tree_rect(F0 &&f, T1 f0, const tree &t) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f(a0, *a1, tree_rect<T1>(f, f0, *a1), *a2,
               tree_rect<T1>(f, f0, *a2));
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &, tree &, T1 &,
                                   tree &, T1 &>
  static T1 tree_rec(F0 &&f, T1 f0, const tree &t) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f(a0, *a1, tree_rec<T1>(f, f0, *a1), *a2,
               tree_rec<T1>(f, f0, *a2));
    } else {
      return f0;
    }
  }

  using priqueue = List<tree>;
  static inline const priqueue empty = List<tree>::nil();
  static tree smash(const tree &t, const tree &u);
  static List<tree> carry(const List<tree> &q, tree t);
  static priqueue insert(unsigned int x, const List<tree> &q);
  static priqueue join(const List<tree> &p, const List<tree> &q, tree c);

  static priqueue unzip(const tree &t,
                        std::function<List<tree>(List<tree>)> cont) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      tree a1_value = *a1;
      tree a2_value = *a2;
      std::function<List<tree>(List<tree>)> f =
          [=](const List<tree> &q) mutable {
            return List<tree>::cons(tree::node(a0, a1_value, tree::leaf()),
                                    cont(q));
          };
      return unzip(a2_value, f);
    } else {
      return cont(List<tree>::nil());
    }
  }

  static priqueue heap_delete_max(const tree &t);
  static key find_max_helper(unsigned int current, const List<tree> &q);
  static std::optional<key> find_max(const List<tree> &q);
  static std::pair<priqueue, priqueue> delete_max_aux(unsigned int m,
                                                      const List<tree> &p);
  static std::optional<std::pair<key, priqueue>>
  delete_max(const List<tree> &q);
  static priqueue merge(const List<tree> &p, const List<tree> &q);
  static priqueue insert_list(const List<unsigned int> &l, List<tree> q);
  static List<unsigned int> make_list(unsigned int n, List<unsigned int> l);
  static key help(const List<tree> &c);
  static inline const key example1 =
      help(merge(insert(5u, insert(3u, insert(7u, List<tree>::nil()))),
                 insert(3u, insert(6u, insert(9u, List<tree>::nil())))));
  static inline const key example2 = help(merge(
      insert_list(make_list(10u, List<unsigned int>::nil()), List<tree>::nil()),
      insert_list(make_list(11u, List<unsigned int>::nil()),
                  List<tree>::nil())));
};

#endif // INCLUDED_BINOMIAL_HEAP
