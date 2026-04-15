#ifndef INCLUDED_MUTUAL_FUNCTOR
#define INCLUDED_MUTUAL_FUNCTOR

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

template <typename M>
concept Elem = requires {
  typename M::t;
  requires(
      requires {
        { M::dflt } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::dflt() } -> std::convertible_to<typename M::t>;
      });
};

template <Elem E> struct MutualTree {
  struct tree;
  struct forest;

  struct tree {
    // TYPES
    struct Leaf {
      unsigned int d_a0;
    };

    struct Node {
      unsigned int d_a0;
      std::shared_ptr<forest> d_a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree> leaf(unsigned int a0) {
      return std::make_shared<tree>(Leaf{std::move(a0)});
    }

    static std::shared_ptr<tree> node(unsigned int a0,
                                      const std::shared_ptr<forest> &a1) {
      return std::make_shared<tree>(Node{std::move(a0), a1});
    }

    static std::shared_ptr<tree> node(unsigned int a0,
                                      std::shared_ptr<forest> &&a1) {
      return std::make_shared<tree>(Node{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  struct forest {
    // TYPES
    struct FNil {};

    struct FCons {
      std::shared_ptr<tree> d_a0;
      std::shared_ptr<forest> d_a1;
    };

    using variant_t = std::variant<FNil, FCons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit forest(FNil _v) : d_v_(_v) {}

    explicit forest(FCons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<forest> fnil() {
      return std::make_shared<forest>(FNil{});
    }

    static std::shared_ptr<forest> fcons(const std::shared_ptr<tree> &a0,
                                         const std::shared_ptr<forest> &a1) {
      return std::make_shared<forest>(FCons{a0, a1});
    }

    static std::shared_ptr<forest> fcons(std::shared_ptr<tree> &&a0,
                                         std::shared_ptr<forest> &&a1) {
      return std::make_shared<forest>(FCons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, std::shared_ptr<forest>> F1>
  static T1 tree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<tree> &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0->v())) {
      const auto &[d_a0] = std::get<typename tree::Leaf>(t0->v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t0->v());
      return f0(d_a0, d_a1);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, std::shared_ptr<forest>> F1>
  static T1 tree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<tree> &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0->v())) {
      const auto &[d_a0] = std::get<typename tree::Leaf>(t0->v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t0->v());
      return f0(d_a0, d_a1);
    }
  }

  template <typename T1,
            MapsTo<T1, std::shared_ptr<tree>, std::shared_ptr<forest>, T1> F1>
  static T1 forest_rect(const T1 f, F1 &&f0,
                        const std::shared_ptr<forest> &f1) {
    if (std::holds_alternative<typename forest::FNil>(f1->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest::FCons>(f1->v());
      return f0(d_a0, d_a1, forest_rect<T1>(f, f0, d_a1));
    }
  }

  template <typename T1,
            MapsTo<T1, std::shared_ptr<tree>, std::shared_ptr<forest>, T1> F1>
  static T1 forest_rec(const T1 f, F1 &&f0, const std::shared_ptr<forest> &f1) {
    if (std::holds_alternative<typename forest::FNil>(f1->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest::FCons>(f1->v());
      return f0(d_a0, d_a1, forest_rec<T1>(f, f0, d_a1));
    }
  }

  __attribute__((pure)) static unsigned int
  tree_size(const std::shared_ptr<tree> &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0->v())) {
      return 1u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t0->v());
      return (1u + forest_size(d_a1));
    }
  }

  __attribute__((pure)) static unsigned int
  forest_size(const std::shared_ptr<forest> &f) {
    if (std::holds_alternative<typename forest::FNil>(f->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest::FCons>(f->v());
      return (tree_size(d_a0) + forest_size(d_a1));
    }
  }

  __attribute__((pure)) static unsigned int
  tree_sum(const std::shared_ptr<tree> &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0->v())) {
      const auto &[d_a0] = std::get<typename tree::Leaf>(t0->v());
      return d_a0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree::Node>(t0->v());
      return (d_a0 + forest_sum(d_a1));
    }
  }

  __attribute__((pure)) static unsigned int
  forest_sum(const std::shared_ptr<forest> &f) {
    if (std::holds_alternative<typename forest::FNil>(f->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest::FCons>(f->v());
      return (tree_sum(d_a0) + forest_sum(d_a1));
    }
  }

  static const std::shared_ptr<tree> &leaf1() {
    static const std::shared_ptr<tree> v = tree::leaf(1u);
    return v;
  }

  static const std::shared_ptr<tree> &leaf2() {
    static const std::shared_ptr<tree> v = tree::leaf(2u);
    return v;
  }

  static const std::shared_ptr<forest> &small_forest() {
    static const std::shared_ptr<forest> v =
        forest::fcons(leaf1(), forest::fcons(leaf2(), forest::fnil()));
    return v;
  }

  static const std::shared_ptr<tree> &sample_tree() {
    static const std::shared_ptr<tree> v = tree::node(0u, small_forest());
    return v;
  }
};

struct NatElem {
  using t = unsigned int;
  static inline const unsigned int dflt = 0u;
};

static_assert(Elem<NatElem>);
using NatTree = MutualTree<NatElem>;
const unsigned int test_tree_size = NatTree::tree_size(NatTree::sample_tree());
const unsigned int test_forest_size =
    NatTree::forest_size(NatTree::small_forest());
const unsigned int test_tree_sum = NatTree::tree_sum(NatTree::sample_tree());

#endif // INCLUDED_MUTUAL_FUNCTOR
