#ifndef INCLUDED_FORWARD_SPEC_ASCII
#define INCLUDED_FORWARD_SPEC_ASCII

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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

    // CREATORS
    explicit node(ANode _v) : d_v_(std::move(_v)) {}

    explicit node(BNode _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<node> ANode_(unsigned int a0) {
        return std::shared_ptr<node>(new node(ANode{a0}));
      }

      static std::shared_ptr<node> BNode_(unsigned int a0) {
        return std::shared_ptr<node>(new node(BNode{a0}));
      }

      static std::unique_ptr<node> ANode_uptr(unsigned int a0) {
        return std::unique_ptr<node>(new node(ANode{a0}));
      }

      static std::unique_ptr<node> BNode_uptr(unsigned int a0) {
        return std::unique_ptr<node>(new node(BNode{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 node_rect(F0 &&f, F1 &&f0, const std::shared_ptr<node> &n) {
    return std::visit(Overloaded{[&](const typename node::ANode _args) -> T1 {
                                   unsigned int n0 = _args.d_a0;
                                   return f(std::move(n0));
                                 },
                                 [&](const typename node::BNode _args) -> T1 {
                                   unsigned int n0 = _args.d_a0;
                                   return f0(std::move(n0));
                                 }},
                      n->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 node_rec(F0 &&f, F1 &&f0, const std::shared_ptr<node> &n) {
    return std::visit(Overloaded{[&](const typename node::ANode _args) -> T1 {
                                   unsigned int n0 = _args.d_a0;
                                   return f(std::move(n0));
                                 },
                                 [&](const typename node::BNode _args) -> T1 {
                                   unsigned int n0 = _args.d_a0;
                                   return f0(std::move(n0));
                                 }},
                      n->v());
  }

  __attribute__((pure)) static unsigned int helper_nat(const unsigned int n);
  __attribute__((pure)) static unsigned int
  bump_node(const std::shared_ptr<node> &x);

  static inline const unsigned int t = bump_node(node::ctor::ANode_(2u));
};

#endif // INCLUDED_FORWARD_SPEC_ASCII
