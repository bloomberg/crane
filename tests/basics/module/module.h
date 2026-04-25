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

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

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
        return tree(Node{clone_as_value<std::unique_ptr<tree>>(d_a0), d_a1,
                         d_a2, clone_as_value<std::unique_ptr<tree>>(d_a3)});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree empty() { return tree(Empty{}); }

    __attribute__((pure)) static tree node(const tree &a0, key a1, value a2,
                                           const tree &a3) {
      return tree(Node{std::make_unique<tree>(a0.clone()), std::move(a1),
                       std::move(a2), std::make_unique<tree>(a3.clone())});
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
