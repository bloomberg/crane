#ifndef INCLUDED_MODULE
#define INCLUDED_MODULE

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

enum class Comparison { e_EQ, e_LT, e_GT };

struct Nat {
  __attribute__((pure)) static Comparison compare(const unsigned int n,
                                                  const unsigned int m);
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
      std::shared_ptr<tree> d_a0;
      key d_a1;
      value d_a2;
      std::shared_ptr<tree> d_a3;
    };

    using variant_t = std::variant<Empty, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Empty _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree> empty() {
      return std::make_shared<tree>(Empty{});
    }

    static std::shared_ptr<tree> node(const std::shared_ptr<tree> &a0, key a1,
                                      value a2,
                                      const std::shared_ptr<tree> &a3) {
      return std::make_shared<tree>(Node{a0, std::move(a1), std::move(a2), a3});
    }

    static std::shared_ptr<tree> node(std::shared_ptr<tree> &&a0, key a1,
                                      value a2, std::shared_ptr<tree> &&a3) {
      return std::make_shared<tree>(
          Node{std::move(a0), std::move(a1), std::move(a2), std::move(a3)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  using t = std::shared_ptr<tree>;

  static const std::shared_ptr<tree> &empty() {
    static const std::shared_ptr<tree> v = tree::empty();
    return v;
  }

  __attribute__((pure)) static t add(const typename K::t k,
                                     const typename V::t v,
                                     const std::shared_ptr<tree> &m) {
    if (std::holds_alternative<typename tree::Empty>(m->v())) {
      return tree::node(tree::empty(), k, v, tree::empty());
    } else {
      const auto &[d_a0, d_a1, d_a2, d_a3] =
          std::get<typename tree::Node>(m->v());
      switch (K::compare(k, d_a1)) {
      case Comparison::e_EQ: {
        return tree::node(d_a0, k, v, d_a3);
      }
      case Comparison::e_LT: {
        return tree::node(add(k, v, d_a0), d_a1, d_a2, d_a3);
      }
      case Comparison::e_GT: {
        return tree::node(d_a0, d_a1, d_a2, add(k, v, d_a3));
      }
      default:
        std::unreachable();
      }
    }
  }

  __attribute__((pure)) static std::optional<value>
  find(const typename K::t k, const std::shared_ptr<tree> &m) {
    if (std::holds_alternative<typename tree::Empty>(m->v())) {
      return std::optional<typename V::t>();
    } else {
      const auto &[d_a0, d_a1, d_a2, d_a3] =
          std::get<typename tree::Node>(m->v());
      switch (K::compare(k, d_a1)) {
      case Comparison::e_EQ: {
        return std::make_optional<typename V::t>(d_a2);
      }
      case Comparison::e_LT: {
        return find(k, d_a0);
      }
      case Comparison::e_GT: {
        return find(k, d_a3);
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
  __attribute__((pure)) static Comparison compare(const unsigned int _x0,
                                                  const unsigned int _x1);
};

static_assert(OrderedType<NatOrdered>);
using NatMap = MakeMap<NatOrdered, NatBase>;
static_assert(Map<NatMap>);
const NatMap::t mymap = NatMap::add(
    1u, 10u, NatMap::add(2u, 20u, NatMap::add(3u, 30u, NatMap::empty())));

#endif // INCLUDED_MODULE
