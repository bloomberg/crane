#ifndef INCLUDED_FORWARD_SPEC_ASCII
#define INCLUDED_FORWARD_SPEC_ASCII

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

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

struct ForwardSpecAscii {
  struct node {
    // TYPES
    struct ANode {
      unsigned int d_a0;
    };

    struct BNode {
      unsigned int d_a0;
    };

    using variant_t = std::variant<ANode, BNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    node() {}

    explicit node(ANode _v) : d_v_(std::move(_v)) {}

    explicit node(BNode _v) : d_v_(std::move(_v)) {}

    node(const node &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    node(node &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) node &operator=(const node &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) node &operator=(node &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) node clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<ANode>(_sv.v())) {
        const auto &[d_a0] = std::get<ANode>(_sv.v());
        return node(ANode{d_a0});
      } else {
        const auto &[d_a0] = std::get<BNode>(_sv.v());
        return node(BNode{d_a0});
      }
    }

    // CREATORS
    __attribute__((pure)) static node anode(unsigned int a0) {
      return node(ANode{std::move(a0)});
    }

    __attribute__((pure)) static node bnode(unsigned int a0) {
      return node(BNode{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) node *operator->() { return this; }

    __attribute__((pure)) const node *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = node(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 node_rect(F0 &&f, F1 &&f0, const node &n) {
    if (std::holds_alternative<typename node::ANode>(n.v())) {
      const auto &[d_a0] = std::get<typename node::ANode>(n.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename node::BNode>(n.v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 node_rec(F0 &&f, F1 &&f0, const node &n) {
    if (std::holds_alternative<typename node::ANode>(n.v())) {
      const auto &[d_a0] = std::get<typename node::ANode>(n.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename node::BNode>(n.v());
      return f0(d_a0);
    }
  }

  __attribute__((pure)) static unsigned int helper_nat(unsigned int n);
  __attribute__((pure)) static unsigned int bump_node(const node &x);
  static inline const unsigned int t = bump_node(node::anode(2u));
};

#endif // INCLUDED_FORWARD_SPEC_ASCII
