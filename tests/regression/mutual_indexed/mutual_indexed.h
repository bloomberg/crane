#ifndef INCLUDED_MUTUAL_INDEXED
#define INCLUDED_MUTUAL_INDEXED

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct MutualIndexed {
  struct EvenTree;
  struct OddTree;

  struct EvenTree {
    // TYPES
    struct ELeaf {};

    struct ENode {
      unsigned int d_n;
      unsigned int d_a1;
      std::unique_ptr<OddTree> d_a2;
    };

    using variant_t = std::variant<ELeaf, ENode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    EvenTree() {}

    explicit EvenTree(ELeaf _v) : d_v_(_v) {}

    explicit EvenTree(ENode _v) : d_v_(std::move(_v)) {}

    EvenTree(const EvenTree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    EvenTree(EvenTree &&_other) : d_v_(std::move(_other.d_v_)) {}

    EvenTree &operator=(const EvenTree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    EvenTree &operator=(EvenTree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    EvenTree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<ELeaf>(_sv.v())) {
        return EvenTree(ELeaf{});
      } else {
        const auto &[d_n, d_a1, d_a2] = std::get<ENode>(_sv.v());
        return EvenTree(
            ENode{d_n, d_a1,
                  d_a2 ? std::make_unique<MutualIndexed::OddTree>(d_a2->clone())
                       : nullptr});
      }
    }

    // CREATORS
    static EvenTree eleaf() { return EvenTree(ELeaf{}); }

    static EvenTree enode(unsigned int n, unsigned int a1, OddTree a2) {
      return EvenTree(ENode{std::move(n), std::move(a1),
                            std::make_unique<OddTree>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  struct OddTree {
    // TYPES
    struct ONode {
      unsigned int d_n;
      unsigned int d_a1;
      std::unique_ptr<EvenTree> d_a2;
    };

    using variant_t = std::variant<ONode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    OddTree() {}

    explicit OddTree(ONode _v) : d_v_(std::move(_v)) {}

    OddTree(const OddTree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    OddTree(OddTree &&_other) : d_v_(std::move(_other.d_v_)) {}

    OddTree &operator=(const OddTree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    OddTree &operator=(OddTree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    OddTree clone() const {
      auto &&_sv = *(this);
      const auto &[d_n, d_a1, d_a2] = std::get<ONode>(_sv.v());
      return OddTree(
          ONode{d_n, d_a1,
                d_a2 ? std::make_unique<MutualIndexed::EvenTree>(d_a2->clone())
                     : nullptr});
    }

    // CREATORS
    static OddTree onode(unsigned int n, unsigned int a1, EvenTree a2) {
      return OddTree(ONode{std::move(n), std::move(a1),
                           std::make_unique<EvenTree>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int, OddTree> F1>
  static T1 EvenTree_rect(const T1 f, F1 &&f0, const unsigned int &,
                          const EvenTree &e) {
    if (std::holds_alternative<typename EvenTree::ELeaf>(e.v())) {
      return f;
    } else {
      const auto &[d_n, d_a1, d_a2] = std::get<typename EvenTree::ENode>(e.v());
      return f0(d_n, d_a1, *(d_a2));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int, OddTree> F1>
  static T1 EvenTree_rec(const T1 f, F1 &&f0, const unsigned int &,
                         const EvenTree &e) {
    if (std::holds_alternative<typename EvenTree::ELeaf>(e.v())) {
      return f;
    } else {
      const auto &[d_n, d_a1, d_a2] = std::get<typename EvenTree::ENode>(e.v());
      return f0(d_n, d_a1, *(d_a2));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int, EvenTree> F0>
  static T1 OddTree_rect(F0 &&f, const unsigned int &, const OddTree &o) {
    const auto &[d_n, d_a1, d_a2] = std::get<typename OddTree::ONode>(o.v());
    return f(d_n, d_a1, *(d_a2));
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int, EvenTree> F0>
  static T1 OddTree_rec(F0 &&f, const unsigned int &, const OddTree &o) {
    const auto &[d_n, d_a1, d_a2] = std::get<typename OddTree::ONode>(o.v());
    return f(d_n, d_a1, *(d_a2));
  }

  static unsigned int even_val(const unsigned int &_x, const EvenTree &t);
  static unsigned int odd_val(const unsigned int &_x, const OddTree &t);
  static inline const EvenTree leaf = EvenTree::eleaf();
  static inline const OddTree tree1 =
      OddTree::onode(0u, 10u, EvenTree::eleaf());
  static inline const EvenTree tree2 =
      EvenTree::enode(1u, 20u, OddTree::onode(0u, 10u, EvenTree::eleaf()));
  static inline const unsigned int test_leaf_val = even_val(0u, leaf);
  static inline const unsigned int test_tree1_val = odd_val(1u, tree1);
  static inline const unsigned int test_tree2_val = even_val(2u, tree2);
};

#endif // INCLUDED_MUTUAL_INDEXED
