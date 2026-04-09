#ifndef INCLUDED_LIST_CLOSURE_ESCAPE
#define INCLUDED_LIST_CLOSURE_ESCAPE

#include <functional>
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

struct ListClosureEscape {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> d_a0;
      unsigned int d_a1;
      std::shared_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree> leaf() {
      return std::make_shared<tree>(Leaf{});
    }

    static std::shared_ptr<tree> node(const std::shared_ptr<tree> &a0,
                                      unsigned int a1,
                                      const std::shared_ptr<tree> &a2) {
      return std::make_shared<tree>(Node{a0, std::move(a1), a2});
    }

    static std::shared_ptr<tree> node(std::shared_ptr<tree> &&a0,
                                      unsigned int a1,
                                      std::shared_ptr<tree> &&a2) {
      return std::make_shared<tree>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    static std::unique_ptr<tree> leaf_uptr() {
      return std::make_unique<tree>(Leaf{});
    }

    static std::unique_ptr<tree> node_uptr(const std::shared_ptr<tree> &a0,
                                           unsigned int a1,
                                           const std::shared_ptr<tree> &a2) {
      return std::make_unique<tree>(Node{a0, std::move(a1), a2});
    }

    static std::unique_ptr<tree> node_uptr(std::shared_ptr<tree> &&a0,
                                           unsigned int a1,
                                           std::shared_ptr<tree> &&a2) {
      return std::make_unique<tree>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int sum_values(const unsigned int x) const {
      return std::visit(
          Overloaded{
              [&](const typename tree::Leaf _args) -> unsigned int {
                return x;
              },
              [&](const typename tree::Node _args) -> unsigned int {
                return std::visit(
                    Overloaded{
                        [&](const typename tree::Leaf _args0) -> unsigned int {
                          return (_args.d_a1 + x);
                        },
                        [&](const typename tree::Node _args0) -> unsigned int {
                          return std::visit(
                              Overloaded{[&](const typename tree::Leaf _args1)
                                             -> unsigned int {
                                           return (_args0.d_a1 + x);
                                         },
                                         [&](const typename tree::Node _args1)
                                             -> unsigned int {
                                           return (
                                               ((_args0.d_a1 + _args1.d_a1) +
                                                _args.d_a1) +
                                               x);
                                         }},
                              _args.d_a2->v());
                        }},
                    _args.d_a0->v());
              }},
          this->v());
    }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    return std::visit(
        Overloaded{[&](const typename tree::Leaf _args) -> T1 { return f; },
                   [&](const typename tree::Node _args) -> T1 {
                     return f0(_args.d_a0, tree_rect<T1>(f, f0, _args.d_a0),
                               _args.d_a1, _args.d_a2,
                               tree_rect<T1>(f, f0, _args.d_a2));
                   }},
        t->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    return std::visit(
        Overloaded{[&](const typename tree::Leaf _args) -> T1 { return f; },
                   [&](const typename tree::Node _args) -> T1 {
                     return f0(_args.d_a0, tree_rec<T1>(f, f0, _args.d_a0),
                               _args.d_a1, _args.d_a2,
                               tree_rec<T1>(f, f0, _args.d_a2));
                   }},
        t->v());
  }

  /// A simple list of closures.
  struct fn_list {
    // TYPES
    struct FNil {};

    struct FCons {
      std::function<unsigned int(unsigned int)> d_a0;
      std::shared_ptr<fn_list> d_a1;
    };

    using variant_t = std::variant<FNil, FCons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit fn_list(FNil _v) : d_v_(std::move(_v)) {}

    explicit fn_list(FCons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<fn_list> fnil() {
      return std::make_shared<fn_list>(FNil{});
    }

    static std::shared_ptr<fn_list>
    fcons(std::function<unsigned int(unsigned int)> a0,
          const std::shared_ptr<fn_list> &a1) {
      return std::make_shared<fn_list>(FCons{std::move(a0), a1});
    }

    static std::shared_ptr<fn_list>
    fcons(std::function<unsigned int(unsigned int)> a0,
          std::shared_ptr<fn_list> &&a1) {
      return std::make_shared<fn_list>(FCons{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<fn_list> fnil_uptr() {
      return std::make_unique<fn_list>(FNil{});
    }

    static std::unique_ptr<fn_list>
    fcons_uptr(std::function<unsigned int(unsigned int)> a0,
               const std::shared_ptr<fn_list> &a1) {
      return std::make_unique<fn_list>(FCons{std::move(a0), a1});
    }

    static std::unique_ptr<fn_list>
    fcons_uptr(std::function<unsigned int(unsigned int)> a0,
               std::shared_ptr<fn_list> &&a1) {
      return std::make_unique<fn_list>(FCons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int apply_first(const unsigned int x) const {
      return std::visit(
          Overloaded{[&](const typename fn_list::FNil _args) -> unsigned int {
                       return x;
                     },
                     [&](const typename fn_list::FCons _args) -> unsigned int {
                       return _args.d_a0(x);
                     }},
          this->v());
    }
  };

  template <typename T1, MapsTo<T1, std::function<unsigned int(unsigned int)>,
                                std::shared_ptr<fn_list>, T1>
                             F1>
  static T1 fn_list_rect(const T1 f, F1 &&f0,
                         const std::shared_ptr<fn_list> &f1) {
    return std::visit(
        Overloaded{[&](const typename fn_list::FNil _args) -> T1 { return f; },
                   [&](const typename fn_list::FCons _args) -> T1 {
                     return f0(_args.d_a0, _args.d_a1,
                               fn_list_rect<T1>(f, f0, _args.d_a1));
                   }},
        f1->v());
  }

  template <typename T1, MapsTo<T1, std::function<unsigned int(unsigned int)>,
                                std::shared_ptr<fn_list>, T1>
                             F1>
  static T1 fn_list_rec(const T1 f, F1 &&f0,
                        const std::shared_ptr<fn_list> &f1) {
    return std::visit(
        Overloaded{[&](const typename fn_list::FNil _args) -> T1 { return f; },
                   [&](const typename fn_list::FCons _args) -> T1 {
                     return f0(_args.d_a0, _args.d_a1,
                               fn_list_rec<T1>(f, f0, _args.d_a1));
                   }},
        f1->v());
  }

  /// BUG: partial applications stored in a custom list via FCons.
  /// Each lambda for (sum_values t_i) captures t_i by &.
  /// When build_fns returns, t1 and t2 are destroyed.
  static std::shared_ptr<fn_list> build_fns(std::shared_ptr<tree> t1,
                                            std::shared_ptr<tree> t2);
  static inline const unsigned int bug_list_clobber = []() {
    std::unique_ptr<tree> t1 =
        tree::node_uptr(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                        tree::node(tree::leaf(), 30u, tree::leaf()));
    std::unique_ptr<tree> t2 =
        tree::node_uptr(tree::node(tree::leaf(), 77u, tree::leaf()), 88u,
                        tree::node(tree::leaf(), 99u, tree::leaf()));
    std::shared_ptr<fn_list> fns = build_fns(std::move(t1), std::move(t2));
    return std::move(fns)->apply_first(0u);
  }();
};

#endif // INCLUDED_LIST_CLOSURE_ESCAPE
