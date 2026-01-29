#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
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
  requires std::same_as<std::remove_cvref_t<decltype(M::dflt)>, typename M::t>;
};

template <Elem E> struct MutualTree {
  struct tree;
  struct forest;
  struct tree {
  public:
    struct Leaf {
      unsigned int _a0;
    };
    struct Node {
      unsigned int _a0;
      std::shared_ptr<forest> _a1;
    };
    using variant_t = std::variant<Leaf, Node>;

  private:
    variant_t v_;
    explicit tree(Leaf _v) : v_(std::move(_v)) {}
    explicit tree(Node _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<tree> Leaf_(unsigned int a0) {
        return std::shared_ptr<tree>(new tree(Leaf{a0}));
      }
      static std::shared_ptr<tree> Node_(unsigned int a0,
                                         const std::shared_ptr<forest> &a1) {
        return std::shared_ptr<tree>(new tree(Node{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };
  struct forest {
  public:
    struct FNil {};
    struct FCons {
      std::shared_ptr<tree> _a0;
      std::shared_ptr<forest> _a1;
    };
    using variant_t = std::variant<FNil, FCons>;

  private:
    variant_t v_;
    explicit forest(FNil _v) : v_(std::move(_v)) {}
    explicit forest(FCons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<forest> FNil_() {
        return std::shared_ptr<forest>(new forest(FNil{}));
      }
      static std::shared_ptr<forest> FCons_(const std::shared_ptr<tree> &a0,
                                            const std::shared_ptr<forest> &a1) {
        return std::shared_ptr<forest>(new forest(FCons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, std::shared_ptr<forest>> F1>
  static T1 tree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<tree> &t0) {
    return std::visit(Overloaded{[&](const typename tree::Leaf _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f(n);
                                 },
                                 [&](const typename tree::Node _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   std::shared_ptr<forest> f1 = _args._a1;
                                   return f0(n, f1);
                                 }},
                      t0->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int, std::shared_ptr<forest>> F1>
  static T1 tree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<tree> &t0) {
    return std::visit(Overloaded{[&](const typename tree::Leaf _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f(n);
                                 },
                                 [&](const typename tree::Node _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   std::shared_ptr<forest> f1 = _args._a1;
                                   return f0(n, f1);
                                 }},
                      t0->v());
  }

  template <typename T1,
            MapsTo<T1, std::shared_ptr<tree>, std::shared_ptr<forest>, T1> F1>
  static T1 forest_rect(const T1 f, F1 &&f0,
                        const std::shared_ptr<forest> &f1) {
    return std::visit(
        Overloaded{[&](const typename forest::FNil _args) -> T1 { return f; },
                   [&](const typename forest::FCons _args) -> T1 {
                     std::shared_ptr<tree> t0 = _args._a0;
                     std::shared_ptr<forest> f2 = _args._a1;
                     return f0(t0, f2, forest_rect<T1>(f, f0, f2));
                   }},
        f1->v());
  }

  template <typename T1,
            MapsTo<T1, std::shared_ptr<tree>, std::shared_ptr<forest>, T1> F1>
  static T1 forest_rec(const T1 f, F1 &&f0, const std::shared_ptr<forest> &f1) {
    return std::visit(
        Overloaded{[&](const typename forest::FNil _args) -> T1 { return f; },
                   [&](const typename forest::FCons _args) -> T1 {
                     std::shared_ptr<tree> t0 = _args._a0;
                     std::shared_ptr<forest> f2 = _args._a1;
                     return f0(t0, f2, forest_rec<T1>(f, f0, f2));
                   }},
        f1->v());
  }

  static unsigned int tree_size(const std::shared_ptr<tree> &t0) {
    return std::visit(
        Overloaded{[](const typename tree::Leaf _args) -> unsigned int {
                     return (0 + 1);
                   },
                   [](const typename tree::Node _args) -> unsigned int {
                     std::shared_ptr<forest> f = _args._a1;
                     return ((0 + 1) + forest_size(f));
                   }},
        t0->v());
  }
  static unsigned int forest_size(const std::shared_ptr<forest> &f) {
    return std::visit(
        Overloaded{
            [](const typename forest::FNil _args) -> unsigned int { return 0; },
            [](const typename forest::FCons _args) -> unsigned int {
              std::shared_ptr<tree> t0 = _args._a0;
              std::shared_ptr<forest> rest = _args._a1;
              return (tree_size(t0) + forest_size(rest));
            }},
        f->v());
  }

  static unsigned int tree_sum(const std::shared_ptr<tree> &t0) {
    return std::visit(
        Overloaded{[](const typename tree::Leaf _args) -> unsigned int {
                     unsigned int n = _args._a0;
                     return n;
                   },
                   [](const typename tree::Node _args) -> unsigned int {
                     unsigned int n = _args._a0;
                     std::shared_ptr<forest> f = _args._a1;
                     return (n + forest_sum(f));
                   }},
        t0->v());
  }
  static unsigned int forest_sum(const std::shared_ptr<forest> &f) {
    return std::visit(
        Overloaded{
            [](const typename forest::FNil _args) -> unsigned int { return 0; },
            [](const typename forest::FCons _args) -> unsigned int {
              std::shared_ptr<tree> t0 = _args._a0;
              std::shared_ptr<forest> rest = _args._a1;
              return (tree_sum(t0) + forest_sum(rest));
            }},
        f->v());
  }

  static inline std::shared_ptr<tree> leaf1 = tree::ctor::Leaf_((0 + 1));

  static inline std::shared_ptr<tree> leaf2 = tree::ctor::Leaf_(((0 + 1) + 1));

  static inline std::shared_ptr<forest> small_forest = forest::ctor::FCons_(
      leaf1, forest::ctor::FCons_(leaf2, forest::ctor::FNil_()));

  static inline std::shared_ptr<tree> sample_tree =
      tree::ctor::Node_(0, small_forest);
};

struct NatElem {
  using t = unsigned int;

  static inline const unsigned int dflt = 0;
};
static_assert(Elem<NatElem>);

using NatTree = MutualTree<NatElem>;

const unsigned int test_tree_size = NatTree::tree_size(NatTree::sample_tree);

const unsigned int test_forest_size =
    NatTree::forest_size(NatTree::small_forest);

const unsigned int test_tree_sum = NatTree::tree_sum(NatTree::sample_tree);
