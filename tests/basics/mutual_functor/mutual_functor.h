#ifndef INCLUDED_MUTUAL_FUNCTOR
#define INCLUDED_MUTUAL_FUNCTOR

#include <concepts>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename M>
concept Elem = requires {
  typename M::t;
  requires(
      requires {
        { M::dflt } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::dflt() } -> std::convertible_to<typename M::t>;
      });
};

template <Elem E> struct MutualTree {
  struct tree;
  struct forest;

  struct tree {
    // TYPES
    struct Leaf {
      unsigned int a0;
    };

    struct Node {
      unsigned int a0;
      std::unique_ptr<forest> a1;
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
      if (std::holds_alternative<Leaf>(this->v())) {
        const auto &[a0] = std::get<Leaf>(this->v());
        return tree(Leaf{a0});
      } else {
        const auto &[a0, a1] = std::get<Node>(this->v());
        return tree(
            Node{a0, a1 ? std::make_unique<MutualTree::forest>(a1->clone())
                        : nullptr});
      }
    }

    // CREATORS
    static tree leaf(unsigned int a0) { return tree(Leaf{a0}); }

    static tree node(unsigned int a0, forest a1) {
      return tree(Node{a0, std::make_unique<forest>(std::move(a1))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.a1) {
            if (std::holds_alternative<typename MutualTree::forest::FCons>(
                    _alt.a1->v())) {
              auto &_palt = std::get<typename MutualTree::forest::FCons>(
                  _alt.a1->v_mut());
              if (_palt.a0) {
                _stack.push_back(std::move(_palt.a0));
              }
            }
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

  struct forest {
    // TYPES
    struct FNil {};

    struct FCons {
      std::unique_ptr<tree> a0;
      std::unique_ptr<forest> a1;
    };

    using variant_t = std::variant<FNil, FCons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    forest() {}

    explicit forest(FNil _v) : v_(_v) {}

    explicit forest(FCons _v) : v_(std::move(_v)) {}

    forest(const forest &_other) : v_(std::move(_other.clone().v_)) {}

    forest(forest &&_other) noexcept : v_(std::move(_other.v_)) {}

    forest &operator=(const forest &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    forest &operator=(forest &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    forest clone() const {
      forest _out{};

      struct _CloneFrame {
        const forest *_src;
        forest *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const forest *_src = _frame._src;
        forest *_dst = _frame._dst;
        if (std::holds_alternative<FNil>(_src->v())) {
          _dst->v_ = FNil{};
        } else {
          const auto &_alt = std::get<FCons>(_src->v());
          _dst->v_ = FCons{
              _alt.a0 ? std::make_unique<MutualTree::tree>(_alt.a0->clone())
                      : nullptr,
              _alt.a1 ? std::make_unique<forest>() : nullptr};
          auto &_dst_alt = std::get<FCons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static forest fnil() { return forest(FNil{}); }

    static forest fcons(tree a0, forest a1) {
      return forest(FCons{std::make_unique<tree>(std::move(a0)),
                          std::make_unique<forest>(std::move(a1))});
    }

    // MANIPULATORS
    ~forest() {
      std::vector<std::unique_ptr<forest>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](forest &_node) {
        if (std::holds_alternative<FCons>(_node.v_)) {
          auto &_alt = std::get<FCons>(_node.v_);
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
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &, forest &>
  static T1 tree_rect(F0 &&f, F1 &&f0, const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      const auto &[a0] = std::get<typename tree::Leaf>(t0.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename tree::Node>(t0.v());
      return f0(a0, *a1);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &, forest &>
  static T1 tree_rec(F0 &&f, F1 &&f0, const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      const auto &[a0] = std::get<typename tree::Leaf>(t0.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename tree::Node>(t0.v());
      return f0(a0, *a1);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, forest &, T1 &>
  static T1 forest_rect(T1 f, F1 &&f0, const forest &f1) {
    if (std::holds_alternative<typename forest::FNil>(f1.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename forest::FCons>(f1.v());
      return f0(*a0, *a1, forest_rect<T1>(f, f0, *a1));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, forest &, T1 &>
  static T1 forest_rec(T1 f, F1 &&f0, const forest &f1) {
    if (std::holds_alternative<typename forest::FNil>(f1.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename forest::FCons>(f1.v());
      return f0(*a0, *a1, forest_rec<T1>(f, f0, *a1));
    }
  }

  static unsigned int tree_size(const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      return 1u;
    } else {
      const auto &[a0, a1] = std::get<typename tree::Node>(t0.v());
      return (1u + forest_size(*a1));
    }
  }

  static unsigned int forest_size(const forest &f) {
    if (std::holds_alternative<typename forest::FNil>(f.v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename forest::FCons>(f.v());
      return (tree_size(*a0) + forest_size(*a1));
    }
  }

  static unsigned int tree_sum(const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      const auto &[a0] = std::get<typename tree::Leaf>(t0.v());
      return a0;
    } else {
      const auto &[a0, a1] = std::get<typename tree::Node>(t0.v());
      return (a0 + forest_sum(*a1));
    }
  }

  static unsigned int forest_sum(const forest &f) {
    if (std::holds_alternative<typename forest::FNil>(f.v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename forest::FCons>(f.v());
      return (tree_sum(*a0) + forest_sum(*a1));
    }
  }

  static const tree &leaf1() {
    static const tree v = tree::leaf(1u);
    return v;
  }

  static const tree &leaf2() {
    static const tree v = tree::leaf(2u);
    return v;
  }

  static const forest &small_forest() {
    static const forest v =
        forest::fcons(leaf1(), forest::fcons(leaf2(), forest::fnil()));
    return v;
  }

  static const tree &sample_tree() {
    static const tree v = tree::node(0u, small_forest());
    return v;
  }
};

struct NatElem {
  using t = unsigned int;
  static inline const unsigned int dflt = 0u;
};

static_assert(Elem<NatElem>);
using NatTree = MutualTree<NatElem>;
const unsigned int test_tree_size = NatTree::tree_size(NatTree::sample_tree());
const unsigned int test_forest_size =
    NatTree::forest_size(NatTree::small_forest());
const unsigned int test_tree_sum = NatTree::tree_sum(NatTree::sample_tree());

#endif // INCLUDED_MUTUAL_FUNCTOR
