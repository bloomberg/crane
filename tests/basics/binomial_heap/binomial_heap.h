#ifndef INCLUDED_BINOMIAL_HEAP
#define INCLUDED_BINOMIAL_HEAP

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
  List clone() const {
    List _out{};

    struct _CloneFrame {
      const List *_src;
      List *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List *_src = _frame._src;
      List *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ =
            Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<List>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1)
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
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
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct BinomialHeap {
  using key = unsigned int;

  struct tree {
    // TYPES
    struct Node {
      key d_a0;
      std::unique_ptr<tree> d_a1;
      std::unique_ptr<tree> d_a2;
    };

    struct Leaf {};

    using variant_t = std::variant<Node, Leaf>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    explicit tree(Leaf _v) : d_v_(_v) {}

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

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Node>(_src->v())) {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node{_alt.d_a0, _alt.d_a1 ? std::make_unique<tree>() : nullptr,
                   _alt.d_a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          if (_alt.d_a2)
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
        } else {
          const auto &_alt = std::get<Leaf>(_src->v());
          _dst->d_v_ = Leaf{};
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
      std::vector<std::unique_ptr<tree>> _stack;
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.d_v_)) {
          auto &_alt = std::get<Node>(_node.d_v_);
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
          if (_alt.d_a2)
            _stack.push_back(std::move(_alt.d_a2));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, tree, T1, tree, T1> F0>
  static T1 tree_rect(F0 &&f, const T1 f0, const tree &t) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f(d_a0, *(d_a1), tree_rect<T1>(f, f0, *(d_a1)), *(d_a2),
               tree_rect<T1>(f, f0, *(d_a2)));
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, tree, T1, tree, T1> F0>
  static T1 tree_rec(F0 &&f, const T1 f0, const tree &t) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f(d_a0, *(d_a1), tree_rec<T1>(f, f0, *(d_a1)), *(d_a2),
               tree_rec<T1>(f, f0, *(d_a2)));
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
                        const std::function<List<tree>(List<tree>)> cont) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      tree d_a1_value = *(d_a1);
      tree d_a2_value = *(d_a2);
      std::function<List<tree>(List<tree>)> f =
          [=](const List<tree> &q) mutable {
            return List<tree>::cons(tree::node(d_a0, d_a1_value, tree::leaf()),
                                    cont(q));
          };
      return unzip(d_a2_value, f);
    } else {
      return cont(List<tree>::nil());
    }
  }

  static priqueue heap_delete_max(const tree &t);
  static key find_max_helper(unsigned int current, const List<tree> &q);
  static std::optional<key> find_max(const List<tree> &q);
  static std::pair<priqueue, priqueue> delete_max_aux(const unsigned int &m,
                                                      const List<tree> &p);
  static std::optional<std::pair<key, priqueue>>
  delete_max(const List<tree> &q);
  static priqueue merge(const List<tree> &p, const List<tree> &q);
  static priqueue insert_list(const List<unsigned int> &l, List<tree> q);
  static List<unsigned int> make_list(const unsigned int &n,
                                      List<unsigned int> l);
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
