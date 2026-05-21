#ifndef INCLUDED_MODULE
#define INCLUDED_MODULE

#include <concepts>
#include <memory>
#include <optional>
#include <utility>
#include <variant>
#include <vector>

enum class Comparison { EQ, LT, GT };

struct Nat {
  static Comparison compare(uint64_t n, uint64_t m);
};

template <typename M>
concept BaseType = requires { typename M::t; };
template <typename M>
concept OrderedType = requires {
  typename M::t;
  {
    M::compare(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<Comparison>;
};
template <typename M>
concept Map = requires {
  typename M::key;
  typename M::value;
  typename M::t;
  requires(
      requires {
        { M::empty } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::empty() } -> std::convertible_to<typename M::t>;
      });
  {
    M::add(std::declval<typename M::key>(), std::declval<typename M::value>(),
           std::declval<typename M::t>())
  } -> std::same_as<typename M::t>;
  {
    M::find(std::declval<typename M::key>(), std::declval<typename M::t>())
  } -> std::same_as<std::optional<typename M::value>>;
};

/// Functor that creates a Map from an OrderedType for keys and
/// a BaseType for values, using a binary search tree internally.
template <OrderedType K, BaseType V> struct MakeMap {
  using key = typename K::t;
  using value = typename V::t;

  struct tree {
    // TYPES
    struct Empty {};

    struct Node {
      std::shared_ptr<tree> a0;
      key a1;
      value a2;
      std::shared_ptr<tree> a3;
    };

    using variant_t = std::variant<Empty, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Empty _v) : v_(_v) {}

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
        if (std::holds_alternative<Empty>(_src->v())) {
          _dst->v_ = Empty{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ =
              Node{_alt.a0 ? std::make_shared<tree>() : nullptr, _alt.a1,
                   _alt.a2, _alt.a3 ? std::make_shared<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a3) {
            _stack.push_back({_alt.a3.get(), _dst_alt.a3.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree empty() { return tree(Empty{}); }

    static tree node(tree a0, key a1, value a2, tree a3) {
      return tree(Node{std::make_shared<tree>(std::move(a0)), std::move(a1),
                       std::move(a2), std::make_shared<tree>(std::move(a3))});
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
          if (_alt.a3) {
            _stack.push_back(std::move(_alt.a3));
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

  using t = tree;

  static const tree &empty() {
    static const tree v = tree::empty();
    return v;
  }

  static t add(typename K::t k, typename V::t v, const tree &m) {
    if (std::holds_alternative<typename tree::Empty>(m.v())) {
      return tree::node(tree::empty(), k, v, tree::empty());
    } else {
      const auto &[a0, a1, a2, a3] = std::get<typename tree::Node>(m.v());
      switch (K::compare(k, a1)) {
      case Comparison::EQ: {
        return tree::node(*a0, k, v, *a3);
      }
      case Comparison::LT: {
        return tree::node(add(k, v, *a0), a1, a2, *a3);
      }
      case Comparison::GT: {
        return tree::node(*a0, a1, a2, add(k, v, *a3));
      }
      default:
        std::unreachable();
      }
    }
  }

  static std::optional<value> find(typename K::t k, const tree &m) {
    if (std::holds_alternative<typename tree::Empty>(m.v())) {
      return std::optional<typename V::t>();
    } else {
      const auto &[a0, a1, a2, a3] = std::get<typename tree::Node>(m.v());
      switch (K::compare(k, a1)) {
      case Comparison::EQ: {
        return std::make_optional<typename V::t>(a2);
      }
      case Comparison::LT: {
        return find(k, *a0);
      }
      case Comparison::GT: {
        return find(k, *a3);
      }
      default:
        std::unreachable();
      }
    }
  }
};

struct NatBase {
  using t = uint64_t;
};

static_assert(BaseType<NatBase>);

struct NatOrdered {
  using t = uint64_t;
  static Comparison compare(uint64_t _x0, uint64_t _x1);
};

static_assert(OrderedType<NatOrdered>);
using NatMap = MakeMap<NatOrdered, NatBase>;
static_assert(Map<NatMap>);
const NatMap::t mymap = NatMap::add(
    UINT64_C(1), UINT64_C(10),
    NatMap::add(UINT64_C(2), UINT64_C(20),
                NatMap::add(UINT64_C(3), UINT64_C(30), NatMap::empty())));

#endif // INCLUDED_MODULE
