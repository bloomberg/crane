#ifndef INCLUDED_MUTUAL_INDEXED
#define INCLUDED_MUTUAL_INDEXED

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct MutualIndexed {
  struct EvenTree;
  struct OddTree;

  struct EvenTree {
    // TYPES
    struct ELeaf {};

    struct ENode {
      uint64_t n;
      uint64_t a1;
      std::shared_ptr<OddTree> a2;
    };

    using variant_t = std::variant<ELeaf, ENode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    EvenTree() {}

    explicit EvenTree(ELeaf _v) : v_(_v) {}

    explicit EvenTree(ENode _v) : v_(std::move(_v)) {}

    static EvenTree eleaf() { return EvenTree(ELeaf{}); }

    static EvenTree enode(uint64_t n, uint64_t a1, OddTree a2) {
      return EvenTree(ENode{n, a1, std::make_shared<OddTree>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct OddTree {
    // TYPES
    struct ONode {
      uint64_t n;
      uint64_t a1;
      std::shared_ptr<EvenTree> a2;
    };

    using variant_t = std::variant<ONode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    OddTree() {}

    explicit OddTree(ONode _v) : v_(std::move(_v)) {}

    static OddTree onode(uint64_t n, uint64_t a1, EvenTree a2) {
      return OddTree(ONode{n, a1, std::make_shared<EvenTree>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, uint64_t &, OddTree &>
  static T1 EvenTree_rect(T1 f, F1 &&f0, uint64_t, const EvenTree &e) {
    if (std::holds_alternative<typename EvenTree::ELeaf>(e.v())) {
      return f;
    } else {
      const auto &[n1, a1, a2] = std::get<typename EvenTree::ENode>(e.v());
      return f0(n1, a1, *a2);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, uint64_t &, OddTree &>
  static T1 EvenTree_rec(T1 f, F1 &&f0, uint64_t, const EvenTree &e) {
    if (std::holds_alternative<typename EvenTree::ELeaf>(e.v())) {
      return f;
    } else {
      const auto &[n1, a1, a2] = std::get<typename EvenTree::ENode>(e.v());
      return f0(n1, a1, *a2);
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &, EvenTree &>
  static T1 OddTree_rect(F0 &&f, uint64_t, const OddTree &o) {
    const auto &[n1, a1, a2] = std::get<typename OddTree::ONode>(o.v());
    return f(n1, a1, *a2);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &, EvenTree &>
  static T1 OddTree_rec(F0 &&f, uint64_t, const OddTree &o) {
    const auto &[n1, a1, a2] = std::get<typename OddTree::ONode>(o.v());
    return f(n1, a1, *a2);
  }

  static uint64_t even_val(uint64_t _x, const EvenTree &t);
  static uint64_t odd_val(uint64_t _x, const OddTree &t);
  static inline const EvenTree leaf = EvenTree::eleaf();
  static inline const OddTree tree1 =
      OddTree::onode(UINT64_C(0), UINT64_C(10), EvenTree::eleaf());
  static inline const EvenTree tree2 = EvenTree::enode(
      UINT64_C(1), UINT64_C(20),
      OddTree::onode(UINT64_C(0), UINT64_C(10), EvenTree::eleaf()));
  static inline const uint64_t test_leaf_val = even_val(UINT64_C(0), leaf);
  static inline const uint64_t test_tree1_val = odd_val(UINT64_C(1), tree1);
  static inline const uint64_t test_tree2_val = even_val(UINT64_C(2), tree2);
};

#endif // INCLUDED_MUTUAL_INDEXED
