#ifndef INCLUDED_MUTUAL_INDEXED
#define INCLUDED_MUTUAL_INDEXED

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

struct MutualIndexed {
  struct EvenTree;
  struct OddTree;

  struct EvenTree {
    // TYPES
    struct ELeaf {};

    struct ENode {
      unsigned int d_a0;
      unsigned int d_a1;
      std::shared_ptr<OddTree> d_a2;
    };

    using variant_t = std::variant<ELeaf, ENode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit EvenTree(ELeaf _v) : d_v_(std::move(_v)) {}

    explicit EvenTree(ENode _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<EvenTree> eleaf() {
      return std::make_shared<EvenTree>(ELeaf{});
    }

    static std::shared_ptr<EvenTree> enode(unsigned int a0, unsigned int a1,
                                           const std::shared_ptr<OddTree> &a2) {
      return std::make_shared<EvenTree>(
          ENode{std::move(a0), std::move(a1), a2});
    }

    static std::shared_ptr<EvenTree> enode(unsigned int a0, unsigned int a1,
                                           std::shared_ptr<OddTree> &&a2) {
      return std::make_shared<EvenTree>(
          ENode{std::move(a0), std::move(a1), std::move(a2)});
    }

    static std::unique_ptr<EvenTree> eleaf_uptr() {
      return std::make_unique<EvenTree>(ELeaf{});
    }

    static std::unique_ptr<EvenTree>
    enode_uptr(unsigned int a0, unsigned int a1,
               const std::shared_ptr<OddTree> &a2) {
      return std::make_unique<EvenTree>(
          ENode{std::move(a0), std::move(a1), a2});
    }

    static std::unique_ptr<EvenTree> enode_uptr(unsigned int a0,
                                                unsigned int a1,
                                                std::shared_ptr<OddTree> &&a2) {
      return std::make_unique<EvenTree>(
          ENode{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  struct OddTree {
    // TYPES
    struct ONode {
      unsigned int d_a0;
      unsigned int d_a1;
      std::shared_ptr<EvenTree> d_a2;
    };

    using variant_t = std::variant<ONode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit OddTree(ONode _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<OddTree> onode(unsigned int a0, unsigned int a1,
                                          const std::shared_ptr<EvenTree> &a2) {
      return std::make_shared<OddTree>(ONode{std::move(a0), std::move(a1), a2});
    }

    static std::shared_ptr<OddTree> onode(unsigned int a0, unsigned int a1,
                                          std::shared_ptr<EvenTree> &&a2) {
      return std::make_shared<OddTree>(
          ONode{std::move(a0), std::move(a1), std::move(a2)});
    }

    static std::unique_ptr<OddTree>
    onode_uptr(unsigned int a0, unsigned int a1,
               const std::shared_ptr<EvenTree> &a2) {
      return std::make_unique<OddTree>(ONode{std::move(a0), std::move(a1), a2});
    }

    static std::unique_ptr<OddTree> onode_uptr(unsigned int a0, unsigned int a1,
                                               std::shared_ptr<EvenTree> &&a2) {
      return std::make_unique<OddTree>(
          ONode{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1,
            MapsTo<T1, unsigned int, unsigned int, std::shared_ptr<OddTree>> F1>
  static T1 EvenTree_rect(const T1 f, F1 &&f0, const unsigned int _x,
                          const std::shared_ptr<EvenTree> &e) {
    return std::visit(
        Overloaded{
            [&](const typename EvenTree::ELeaf _args) -> T1 { return f; },
            [&](const typename EvenTree::ENode _args) -> T1 {
              return f0(_args.d_a0, _args.d_a1, _args.d_a2);
            }},
        e->v());
  }

  template <typename T1,
            MapsTo<T1, unsigned int, unsigned int, std::shared_ptr<OddTree>> F1>
  static T1 EvenTree_rec(const T1 f, F1 &&f0, const unsigned int _x,
                         const std::shared_ptr<EvenTree> &e) {
    return std::visit(
        Overloaded{
            [&](const typename EvenTree::ELeaf _args) -> T1 { return f; },
            [&](const typename EvenTree::ENode _args) -> T1 {
              return f0(_args.d_a0, _args.d_a1, _args.d_a2);
            }},
        e->v());
  }

  template <
      typename T1,
      MapsTo<T1, unsigned int, unsigned int, std::shared_ptr<EvenTree>> F0>
  static T1 OddTree_rect(F0 &&f, const unsigned int _x,
                         const std::shared_ptr<OddTree> &o) {
    return std::visit(
        Overloaded{[&](const typename OddTree::ONode _args) -> T1 {
          return f(_args.d_a0, _args.d_a1, _args.d_a2);
        }},
        o->v());
  }

  template <
      typename T1,
      MapsTo<T1, unsigned int, unsigned int, std::shared_ptr<EvenTree>> F0>
  static T1 OddTree_rec(F0 &&f, const unsigned int _x,
                        const std::shared_ptr<OddTree> &o) {
    return std::visit(
        Overloaded{[&](const typename OddTree::ONode _args) -> T1 {
          return f(_args.d_a0, _args.d_a1, _args.d_a2);
        }},
        o->v());
  }

  __attribute__((pure)) static unsigned int
  even_val(const unsigned int _x, const std::shared_ptr<EvenTree> &t);
  __attribute__((pure)) static unsigned int
  odd_val(const unsigned int _x, const std::shared_ptr<OddTree> &t);
  static inline const std::shared_ptr<EvenTree> leaf = EvenTree::eleaf();
  static inline const std::shared_ptr<OddTree> tree1 =
      OddTree::onode(0u, 10u, EvenTree::eleaf());
  static inline const std::shared_ptr<EvenTree> tree2 =
      EvenTree::enode(1u, 20u, OddTree::onode(0u, 10u, EvenTree::eleaf()));
  static inline const unsigned int test_leaf_val = even_val(0u, leaf);
  static inline const unsigned int test_tree1_val = odd_val(1u, tree1);
  static inline const unsigned int test_tree2_val = even_val(2u, tree2);
};

#endif // INCLUDED_MUTUAL_INDEXED
