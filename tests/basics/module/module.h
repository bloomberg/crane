#ifndef INCLUDED_MODULE
#define INCLUDED_MODULE

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

enum class Comparison { e_EQ, e_LT, e_GT };

struct Nat {
  __attribute__((pure)) static Comparison compare(const unsigned int &n,
                                                  const unsigned int &m);
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
      std::unique_ptr<tree> d_a0;
      key d_a1;
      value d_a2;
      std::unique_ptr<tree> d_a3;
    };

    using variant_t = std::variant<Empty, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Empty _v) : d_v_(_v) {}

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
      if (std::holds_alternative<Empty>(_sv.v())) {
        return tree(Empty{});
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3] = std::get<Node>(_sv.v());
        return tree(Node{
            d_a0 ? std::make_unique<MakeMap::tree>(d_a0->clone()) : nullptr,
            [](auto &&__v) -> key {
              if constexpr (
                  requires { __v ? 0 : 0; } && requires { *__v; } &&
                  requires { __v->clone(); } && requires { __v.get(); }) {
                using _E = std::remove_cvref_t<decltype(*__v)>;
                return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
              } else if constexpr (requires { __v.clone(); }) {
                return __v.clone();
              } else {
                return __v;
              }
            }(d_a1),
            [](auto &&__v) -> value {
              if constexpr (
                  requires { __v ? 0 : 0; } && requires { *__v; } &&
                  requires { __v->clone(); } && requires { __v.get(); }) {
                using _E = std::remove_cvref_t<decltype(*__v)>;
                return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
              } else if constexpr (requires { __v.clone(); }) {
                return __v.clone();
              } else {
                return __v;
              }
            }(d_a2),
            d_a3 ? std::make_unique<MakeMap::tree>(d_a3->clone()) : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree empty() { return tree(Empty{}); }

    __attribute__((pure)) static tree node(const tree &a0, key a1, value a2,
                                           const tree &a3) {
      return tree(Node{std::make_unique<tree>(a0), std::move(a1), std::move(a2),
                       std::make_unique<tree>(a3)});
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

  using t = tree;

  static const tree &empty() {
    static const tree v = tree::empty();
    return v;
  }

  __attribute__((pure)) static t add(const typename K::t k,
                                     const typename V::t v, const tree &m) {
    if (std::holds_alternative<typename tree::Empty>(m.v())) {
      return tree::node(tree::empty(), k, v, tree::empty());
    } else {
      const auto &[d_a0, d_a1, d_a2, d_a3] =
          std::get<typename tree::Node>(m.v());
      switch (K::compare(k, d_a1)) {
      case Comparison::e_EQ: {
        return tree::node(*(d_a0), k, v, *(d_a3));
      }
      case Comparison::e_LT: {
        return tree::node(add(k, v, *(d_a0)), d_a1, d_a2, *(d_a3));
      }
      case Comparison::e_GT: {
        return tree::node(*(d_a0), d_a1, d_a2, add(k, v, *(d_a3)));
      }
      default:
        std::unreachable();
      }
    }
  }

  __attribute__((pure)) static std::optional<value> find(const typename K::t k,
                                                         const tree &m) {
    if (std::holds_alternative<typename tree::Empty>(m.v())) {
      return std::optional<typename V::t>();
    } else {
      const auto &[d_a0, d_a1, d_a2, d_a3] =
          std::get<typename tree::Node>(m.v());
      switch (K::compare(k, d_a1)) {
      case Comparison::e_EQ: {
        return std::make_optional<typename V::t>(d_a2);
      }
      case Comparison::e_LT: {
        return find(k, *(d_a0));
      }
      case Comparison::e_GT: {
        return find(k, *(d_a3));
      }
      default:
        std::unreachable();
      }
    }
  }
};

struct NatBase {
  using t = unsigned int;
};

static_assert(BaseType<NatBase>);

struct NatOrdered {
  using t = unsigned int;
  __attribute__((pure)) static Comparison compare(const unsigned int &_x0,
                                                  const unsigned int &_x1);
};

static_assert(OrderedType<NatOrdered>);
using NatMap = MakeMap<NatOrdered, NatBase>;
static_assert(Map<NatMap>);
const NatMap::t mymap = NatMap::add(
    1u, 10u, NatMap::add(2u, 20u, NatMap::add(3u, 30u, NatMap::empty())));

#endif // INCLUDED_MODULE
