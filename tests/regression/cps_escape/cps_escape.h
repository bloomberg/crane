#ifndef INCLUDED_CPS_ESCAPE
#define INCLUDED_CPS_ESCAPE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct CpsEscape {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> d_a0;
      unsigned int d_a1;
      std::unique_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : d_v_(_v) {}

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
          _dst->d_v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node{_alt.d_a0 ? std::make_unique<tree>() : nullptr, _alt.d_a1,
                   _alt.d_a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), std::move(a1),
                       std::make_unique<tree>(std::move(a2))});
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
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
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

    /// CPS-style: take a tree, produce a continuation (nat -> nat)
    /// that adds tree_sum to its argument. The continuation captures t.
    unsigned int make_adder(const unsigned int &x) const {
      return ((*(this)).tree_sum() + x);
    }

    /// Sum all values in a tree.
    unsigned int tree_sum() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return (((*(d_a0)).tree_sum() + d_a1) + (*(d_a2)).tree_sum());
      }
    }

    template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
    T1 tree_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template tree_rec<T1>(f, f0), d_a1,
                  *(d_a2), (*(d_a2)).template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
    T1 tree_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template tree_rect<T1>(f, f0), d_a1,
                  *(d_a2), (*(d_a2)).template tree_rect<T1>(f, f0));
      }
    }
  };

  struct box {
    // TYPES
    struct Box0 {
      std::function<unsigned int(unsigned int)> d_a0;
    };

    using variant_t = std::variant<Box0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    box() {}

    explicit box(Box0 _v) : d_v_(std::move(_v)) {}

    box(const box &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    box(box &&_other) : d_v_(std::move(_other.d_v_)) {}

    box &operator=(const box &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    box &operator=(box &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    box clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<Box0>(_sv.v());
      return box(Box0{d_a0});
    }

    // CREATORS
    static box box0(std::function<unsigned int(unsigned int)> a0) {
      return box(Box0{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    template <typename T1,
              MapsTo<T1, std::function<unsigned int(unsigned int)>> F0>
    T1 box_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<typename box::Box0>(_sv.v());
      return f(d_a0);
    }

    template <typename T1,
              MapsTo<T1, std::function<unsigned int(unsigned int)>> F0>
    T1 box_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<typename box::Box0>(_sv.v());
      return f(d_a0);
    }
  };

  /// Store the continuation in a Box. The function receives the closure
  /// as an argument and wraps it - the closure flows THROUGH a parameter.
  template <MapsTo<unsigned int, unsigned int> F0>
  static box store_in_box(F0 &&f) {
    return box::box0(f);
  }

  /// BUG HYPOTHESIS: make_adder creates &t lambda.
  /// store_in_box receives it and puts it in Box.
  /// When cps_escape returns, t is destroyed but Box holds the lambda.
  ///
  /// Expected: tree_sum(Node(Node(Leaf,10,Leaf), 20, Node(Leaf,30,Leaf)))
  /// = 10 + 20 + 30 = 60
  /// adder 5 = 60 + 5 = 65
  static inline const unsigned int cps_escape = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                          tree::node(tree::leaf(), 30u, tree::leaf()));
      std::function<unsigned int(unsigned int)> adder =
          [=](unsigned int _x0) mutable -> unsigned int {
        return t.make_adder(_x0);
      };
      box b = store_in_box(adder);
      auto &[d_a0] = std::get<typename box::Box0>(b.v_mut());
      return d_a0(5u);
    }();
  }();
  /// Same but inline: no intermediate let for adder.
  /// The closure goes directly from make_adder into store_in_box.
  static inline const unsigned int cps_escape_inline = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                          tree::node(tree::leaf(), 30u, tree::leaf()));
      box b = store_in_box([=](unsigned int _x0) mutable -> unsigned int {
        return t.make_adder(_x0);
      });
      auto &[d_a0] = std::get<typename box::Box0>(b.v_mut());
      return d_a0(5u);
    }();
  }();
  /// CPS with two stored continuations.
  /// Build two adders from different trees and store both.
  static inline const unsigned int cps_escape_two = []() {
    return []() {
      tree t1 = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                           tree::node(tree::leaf(), 30u, tree::leaf()));
      tree t2 = tree::node(tree::leaf(), 100u, tree::leaf());
      box b1 = store_in_box([=](unsigned int _x0) mutable -> unsigned int {
        return t1.make_adder(_x0);
      });
      box b2 = store_in_box([=](unsigned int _x0) mutable -> unsigned int {
        return t2.make_adder(_x0);
      });
      auto &[d_a0] = std::get<typename box::Box0>(b1.v_mut());
      auto &[d_a00] = std::get<typename box::Box0>(b2.v_mut());
      return (d_a0(0u) + d_a00(0u));
    }();
  }();
};

#endif // INCLUDED_CPS_ESCAPE
