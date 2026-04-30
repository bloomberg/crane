#ifndef INCLUDED_MUTUAL_FUNCTOR
#define INCLUDED_MUTUAL_FUNCTOR

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
      unsigned int d_a0;
    };

    struct Node {
      unsigned int d_a0;
      std::unique_ptr<forest> d_a1;
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
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<Leaf>(_sv.v());
        return tree(Leaf{d_a0});
      } else {
        const auto &[d_a0, d_a1] = std::get<Node>(_sv.v());
        return tree(Node{
            d_a0, d_a1 ? std::make_unique<MutualTree::forest>(d_a1->clone())
                       : nullptr});
      }
    }

    // CREATORS
    static tree leaf(unsigned int a0) { return tree(Leaf{std::move(a0)}); }

    static tree node(unsigned int a0, forest a1) {
      return tree(Node{std::move(a0), std::make_unique<forest>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  struct forest {
    // TYPES
    struct FNil {};

    struct FCons {
      std::unique_ptr<tree> d_a0;
      std::unique_ptr<forest> d_a1;
    };

    using variant_t = std::variant<FNil, FCons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    forest() {}

    explicit forest(FNil _v) : d_v_(_v) {}

    explicit forest(FCons _v) : d_v_(std::move(_v)) {}

    forest(const forest &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    forest(forest &&_other) : d_v_(std::move(_other.d_v_)) {}

    forest &operator=(const forest &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    forest &operator=(forest &&_other) {
      d_v_ = std::move(_other.d_v_);
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
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const forest *_src = _frame._src;
        forest *_dst = _frame._dst;
        if (std::holds_alternative<FNil>(_src->v())) {
          _dst->d_v_ = FNil{};
        } else {
          const auto &_alt = std::get<FCons>(_src->v());
          _dst->d_v_ = FCons{
              _alt.d_a0 ? std::make_unique<MutualTree::tree>(_alt.d_a0->clone())
                        : nullptr,
              _alt.d_a1 ? std::make_unique<forest>() : nullptr};
          auto &_dst_alt = std::get<FCons>(_dst->d_v_);
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
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
      auto _drain = [&](forest &_node) {
        if (std::holds_alternative<FCons>(_node.d_v_)) {
          auto &_alt = std::get<FCons>(_node.d_v_);
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
            MapsTo<T1, unsigned int, forest> F1>
  static T1 tree_rect(F0 &&f, F1 &&f0, const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      const auto &[d_a0] = std::get<typename tree::Leaf>(t0.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t0.v());
      return f0(d_a0, *(d_a1));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, forest> F1>
  static T1 tree_rec(F0 &&f, F1 &&f0, const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      const auto &[d_a0] = std::get<typename tree::Leaf>(t0.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t0.v());
      return f0(d_a0, *(d_a1));
    }
  }

  template <typename T1, MapsTo<T1, tree, forest, T1> F1>
  static T1 forest_rect(const T1 f, F1 &&f0, const forest &f1) {
    if (std::holds_alternative<typename forest::FNil>(f1.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest::FCons>(f1.v());
      return f0(*(d_a0), *(d_a1), forest_rect<T1>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, MapsTo<T1, tree, forest, T1> F1>
  static T1 forest_rec(const T1 f, F1 &&f0, const forest &f1) {
    if (std::holds_alternative<typename forest::FNil>(f1.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest::FCons>(f1.v());
      return f0(*(d_a0), *(d_a1), forest_rec<T1>(f, f0, *(d_a1)));
    }
  }

  static unsigned int tree_size(const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      return 1u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t0.v());
      return (1u + forest_size(*(d_a1)));
    }
  }

  static unsigned int forest_size(const forest &f) {
    if (std::holds_alternative<typename forest::FNil>(f.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest::FCons>(f.v());
      return (tree_size(*(d_a0)) + forest_size(*(d_a1)));
    }
  }

  static unsigned int tree_sum(const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      const auto &[d_a0] = std::get<typename tree::Leaf>(t0.v());
      return d_a0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t0.v());
      return (d_a0 + forest_sum(*(d_a1)));
    }
  }

  static unsigned int forest_sum(const forest &f) {
    if (std::holds_alternative<typename forest::FNil>(f.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest::FCons>(f.v());
      return (tree_sum(*(d_a0)) + forest_sum(*(d_a1)));
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
