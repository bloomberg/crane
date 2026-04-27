#ifndef INCLUDED_FORWARD_SPEC_ASCII
#define INCLUDED_FORWARD_SPEC_ASCII

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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

    node &operator=(const node &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    node &operator=(node &&_other) {
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
    inline variant_t &v_mut() { return d_v_; }

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
