#ifndef INCLUDED_FORWARD_SPEC_ASCII
#define INCLUDED_FORWARD_SPEC_ASCII

#include <type_traits>
#include <utility>
#include <variant>

struct ForwardSpecAscii {
  struct node {
    // TYPES
    struct ANode {
      unsigned int a0;
    };

    struct BNode {
      unsigned int a0;
    };

    using variant_t = std::variant<ANode, BNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    node() {}

    explicit node(ANode _v) : v_(std::move(_v)) {}

    explicit node(BNode _v) : v_(std::move(_v)) {}

    node(const node &_other) : v_(std::move(_other.clone().v_)) {}

    node(node &&_other) : v_(std::move(_other.v_)) {}

    node &operator=(const node &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    node &operator=(node &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    node clone() const {
      if (std::holds_alternative<ANode>(this->v())) {
        const auto &[a0] = std::get<ANode>(this->v());
        return node(ANode{a0});
      } else {
        const auto &[a0] = std::get<BNode>(this->v());
        return node(BNode{a0});
      }
    }

    // CREATORS
    static node anode(unsigned int a0) { return node(ANode{a0}); }

    static node bnode(unsigned int a0) { return node(BNode{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &>
  static T1 node_rect(F0 &&f, F1 &&f0, const node &n) {
    if (std::holds_alternative<typename node::ANode>(n.v())) {
      const auto &[a0] = std::get<typename node::ANode>(n.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename node::BNode>(n.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &>
  static T1 node_rec(F0 &&f, F1 &&f0, const node &n) {
    if (std::holds_alternative<typename node::ANode>(n.v())) {
      const auto &[a0] = std::get<typename node::ANode>(n.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename node::BNode>(n.v());
      return f0(a0);
    }
  }

  static unsigned int helper_nat(unsigned int n);
  static unsigned int bump_node(const node &x);
  static inline const unsigned int t = bump_node(node::anode(2u));
};

#endif // INCLUDED_FORWARD_SPEC_ASCII
