#ifndef INCLUDED_MUTUAL_FUNCTOR
#define INCLUDED_MUTUAL_FUNCTOR

#include <any>
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
      uint64_t a0;
    };

    struct Node {
      uint64_t a0;
      std::shared_ptr<forest> a1;
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

    static tree leaf(uint64_t a0) { return tree(Leaf{a0}); }

    static tree node(uint64_t a0, forest a1) {
      return tree(Node{a0, std::make_shared<forest>(std::move(a1))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = std::any_cast<std::shared_ptr<tree>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = std::any_cast<std::shared_ptr<forest>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename forest::FCons>(&_pv)) {
                if (_alt->a0) {
                  _stack.push_back(std::move(_alt->a0));
                }
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
            }
          }
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
      std::shared_ptr<tree> a0;
      std::shared_ptr<forest> a1;
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

    static forest fnil() { return forest(FNil{}); }

    static forest fcons(tree a0, forest a1) {
      return forest(FCons{std::make_shared<tree>(std::move(a0)),
                          std::make_shared<forest>(std::move(a1))});
    }

    // MANIPULATORS
    ~forest() {
      std::vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<FCons>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = std::any_cast<std::shared_ptr<forest>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = std::any_cast<std::shared_ptr<tree>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename tree::Node>(&_pv)) {
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
            }
          }
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &, forest &>
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
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &, forest &>
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

  static uint64_t tree_size(const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      return UINT64_C(1);
    } else {
      const auto &[a0, a1] = std::get<typename tree::Node>(t0.v());
      return (UINT64_C(1) + forest_size(*a1));
    }
  }

  static uint64_t forest_size(const forest &f) {
    if (std::holds_alternative<typename forest::FNil>(f.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename forest::FCons>(f.v());
      return (tree_size(*a0) + forest_size(*a1));
    }
  }

  static uint64_t tree_sum(const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      const auto &[a0] = std::get<typename tree::Leaf>(t0.v());
      return a0;
    } else {
      const auto &[a0, a1] = std::get<typename tree::Node>(t0.v());
      return (a0 + forest_sum(*a1));
    }
  }

  static uint64_t forest_sum(const forest &f) {
    if (std::holds_alternative<typename forest::FNil>(f.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename forest::FCons>(f.v());
      return (tree_sum(*a0) + forest_sum(*a1));
    }
  }

  static const tree &leaf1() {
    static const tree v = tree::leaf(UINT64_C(1));
    return v;
  }

  static const tree &leaf2() {
    static const tree v = tree::leaf(UINT64_C(2));
    return v;
  }

  static const forest &small_forest() {
    static const forest v =
        forest::fcons(leaf1(), forest::fcons(leaf2(), forest::fnil()));
    return v;
  }

  static const tree &sample_tree() {
    static const tree v = tree::node(UINT64_C(0), small_forest());
    return v;
  }
};

struct NatElem {
  using t = uint64_t;
  static inline const uint64_t dflt = UINT64_C(0);
};

static_assert(Elem<NatElem>);
using NatTree = MutualTree<NatElem>;
const uint64_t test_tree_size = NatTree::tree_size(NatTree::sample_tree());
const uint64_t test_forest_size = NatTree::forest_size(NatTree::small_forest());

const uint64_t test_tree_sum = NatTree::tree_sum(NatTree::sample_tree());

#endif // INCLUDED_MUTUAL_FUNCTOR
