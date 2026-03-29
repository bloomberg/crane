#ifndef INCLUDED_FORWARD_SPEC_ASCII
#define INCLUDED_FORWARD_SPEC_ASCII

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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
    explicit node(ANode _v) : d_v_(std::move(_v)) {}

    explicit node(BNode _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<node> anode(unsigned int a0) {
      return std::make_shared<node>(ANode{std::move(a0)});
    }

    static std::shared_ptr<node> bnode(unsigned int a0) {
      return std::make_shared<node>(BNode{std::move(a0)});
    }

    static std::unique_ptr<node> anode_uptr(unsigned int a0) {
      return std::make_unique<node>(ANode{std::move(a0)});
    }

    static std::unique_ptr<node> bnode_uptr(unsigned int a0) {
      return std::make_unique<node>(BNode{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 node_rect(F0 &&f, F1 &&f0, const std::shared_ptr<node> &n) {
    return std::visit(Overloaded{[&](const typename node::ANode _args) -> T1 {
                                   return f(_args.d_a0);
                                 },
                                 [&](const typename node::BNode _args) -> T1 {
                                   return f0(_args.d_a0);
                                 }},
                      n->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 node_rec(F0 &&f, F1 &&f0, const std::shared_ptr<node> &n) {
    return std::visit(Overloaded{[&](const typename node::ANode _args) -> T1 {
                                   return f(_args.d_a0);
                                 },
                                 [&](const typename node::BNode _args) -> T1 {
                                   return f0(_args.d_a0);
                                 }},
                      n->v());
  }

  __attribute__((pure)) static unsigned int helper_nat(const unsigned int n);
  __attribute__((pure)) static unsigned int
  bump_node(const std::shared_ptr<node> &x);

  static inline const unsigned int t = bump_node(node::anode(2u));
};

#endif // INCLUDED_FORWARD_SPEC_ASCII
