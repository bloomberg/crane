#ifndef INCLUDED_TREE
#define INCLUDED_TREE

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

enum class Bool0 { e_TRUE0, e_FALSE0 };

struct Nat : public std::enable_shared_from_this<Nat> {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit Nat(O _v) : d_v_(std::move(_v)) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Nat> O_() {
      return std::shared_ptr<Nat>(new Nat(O{}));
    }

    static std::shared_ptr<Nat> S_(const std::shared_ptr<Nat> &a0) {
      return std::shared_ptr<Nat>(new Nat(S{a0}));
    }

    static std::unique_ptr<Nat> O_uptr() {
      return std::unique_ptr<Nat>(new Nat(O{}));
    }

    static std::unique_ptr<Nat> S_uptr(const std::shared_ptr<Nat> &a0) {
      return std::unique_ptr<Nat>(new Nat(S{a0}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<Nat> max(std::shared_ptr<Nat> m) const {
    return std::visit(
        Overloaded{
            [&](const typename Nat::O _args) -> std::shared_ptr<Nat> {
              return m;
            },
            [&](const typename Nat::S _args) -> std::shared_ptr<Nat> {
              std::shared_ptr<Nat> n_ = _args.d_a0;
              return std::visit(
                  Overloaded{
                      [&](const typename Nat::O _args) -> std::shared_ptr<Nat> {
                        return std::const_pointer_cast<Nat>(
                            this->shared_from_this());
                      },
                      [&](const typename Nat::S _args) -> std::shared_ptr<Nat> {
                        std::shared_ptr<Nat> m_ = _args.d_a0;
                        return Nat::ctor::S_(std::move(n_)->max(std::move(m_)));
                      }},
                  m->v());
            }},
        this->v());
  }

  std::shared_ptr<Nat> add(std::shared_ptr<Nat> m) const {
    return std::visit(
        Overloaded{[&](const typename Nat::O _args) -> std::shared_ptr<Nat> {
                     return m;
                   },
                   [&](const typename Nat::S _args) -> std::shared_ptr<Nat> {
                     std::shared_ptr<Nat> p = _args.d_a0;
                     return Nat::ctor::S_(std::move(p)->add(m));
                   }},
        this->v());
  }
};

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    return std::visit(
        Overloaded{[&](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<t_A>> { return m; },
                   [&](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<t_A>> {
                     t_A a = _args.d_a0;
                     std::shared_ptr<List<t_A>> l1 = _args.d_a1;
                     return List<t_A>::ctor::Cons_(a, std::move(l1)->app(m));
                   }},
        this->v());
  }
};

struct Tree {
  /// A polymorphic binary tree. A tree is either a leaf or a
  /// node with a left subtree, a value, and a right subtree.
  template <typename t_A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree<t_A>> d_a0;
      t_A d_a1;
      std::shared_ptr<tree<t_A>> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<tree<t_A>> Leaf_() {
        return std::shared_ptr<tree<t_A>>(new tree<t_A>(Leaf{}));
      }

      static std::shared_ptr<tree<t_A>>
      Node_(const std::shared_ptr<tree<t_A>> &a0, t_A a1,
            const std::shared_ptr<tree<t_A>> &a2) {
        return std::shared_ptr<tree<t_A>>(new tree<t_A>(Node{a0, a1, a2}));
      }

      static std::unique_ptr<tree<t_A>> Leaf_uptr() {
        return std::unique_ptr<tree<t_A>>(new tree<t_A>(Leaf{}));
      }

      static std::unique_ptr<tree<t_A>>
      Node_uptr(const std::shared_ptr<tree<t_A>> &a0, t_A a1,
                const std::shared_ptr<tree<t_A>> &a2) {
        return std::unique_ptr<tree<t_A>>(new tree<t_A>(Node{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, std::shared_ptr<tree<t_A>>, T1, t_A,
                                  std::shared_ptr<tree<t_A>>, T1>
                               F1>
    T1 tree_rec(const T1 f, F1 &&f0) const {
      return std::visit(
          Overloaded{
              [&](const typename tree<t_A>::Leaf _args) -> T1 { return f; },
              [&](const typename tree<t_A>::Node _args) -> T1 {
                std::shared_ptr<tree<t_A>> t0 = _args.d_a0;
                t_A y = _args.d_a1;
                std::shared_ptr<tree<t_A>> t1 = _args.d_a2;
                return f0(t0, t0->template tree_rec<T1>(f, f0), y, t1,
                          t1->template tree_rec<T1>(f, f0));
              }},
          this->v());
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<tree<t_A>>, T1, t_A,
                                  std::shared_ptr<tree<t_A>>, T1>
                               F1>
    T1 tree_rect(const T1 f, F1 &&f0) const {
      return std::visit(
          Overloaded{
              [&](const typename tree<t_A>::Leaf _args) -> T1 { return f; },
              [&](const typename tree<t_A>::Node _args) -> T1 {
                std::shared_ptr<tree<t_A>> t0 = _args.d_a0;
                t_A y = _args.d_a1;
                std::shared_ptr<tree<t_A>> t1 = _args.d_a2;
                return f0(t0, t0->template tree_rect<T1>(f, f0), y, t1,
                          t1->template tree_rect<T1>(f, f0));
              }},
          this->v());
    }

    /// Returns true if t is a leaf, false otherwise.
    __attribute__((pure)) Bool0 is_leaf() const {
      return std::visit(
          Overloaded{[](const typename tree<t_A>::Leaf _args) -> Bool0 {
                       return Bool0::e_TRUE0;
                     },
                     [](const typename tree<t_A>::Node _args) -> Bool0 {
                       return Bool0::e_FALSE0;
                     }},
          this->v());
    }

    /// Number of nodes in tree t. A leaf counts as 1.
    std::shared_ptr<Nat> size() const {
      return std::visit(
          Overloaded{
              [](const typename tree<t_A>::Leaf _args) -> std::shared_ptr<Nat> {
                return Nat::ctor::S_(Nat::ctor::O_());
              },
              [](const typename tree<t_A>::Node _args) -> std::shared_ptr<Nat> {
                std::shared_ptr<tree<t_A>> l = _args.d_a0;
                std::shared_ptr<tree<t_A>> r = _args.d_a2;
                return Nat::ctor::S_(Nat::ctor::O_())
                    ->add(std::move(l)->size())
                    ->add(std::move(r)->size());
              }},
          this->v());
    }

    /// Height of tree t. A leaf has height 1.
    std::shared_ptr<Nat> height() const {
      return std::visit(
          Overloaded{
              [](const typename tree<t_A>::Leaf _args) -> std::shared_ptr<Nat> {
                return Nat::ctor::S_(Nat::ctor::O_());
              },
              [](const typename tree<t_A>::Node _args) -> std::shared_ptr<Nat> {
                std::shared_ptr<tree<t_A>> l = _args.d_a0;
                std::shared_ptr<tree<t_A>> r = _args.d_a2;
                return Nat::ctor::S_(Nat::ctor::O_())
                    ->add(std::move(l)->height()->max(std::move(r)->height()));
              }},
          this->v());
    }

    /// Collect all values in t into a list via in-order traversal.
    std::shared_ptr<List<t_A>> flatten() const {
      return std::visit(
          Overloaded{[](const typename tree<t_A>::Leaf _args)
                         -> std::shared_ptr<List<t_A>> {
                       return List<t_A>::ctor::Nil_();
                     },
                     [](const typename tree<t_A>::Node _args)
                         -> std::shared_ptr<List<t_A>> {
                       std::shared_ptr<tree<t_A>> l = _args.d_a0;
                       t_A x = _args.d_a1;
                       std::shared_ptr<tree<t_A>> r = _args.d_a2;
                       return std::move(l)->flatten()->app(
                           List<t_A>::ctor::Cons_(x, std::move(r)->flatten()));
                     }},
          this->v());
    }

    /// Merge two trees t1 and t2 element-wise using combine.
    /// Subtrees beyond the shape of the other tree are truncated.
    template <MapsTo<t_A, t_A, t_A> F0>
    std::shared_ptr<tree<t_A>>
    merge(F0 &&combine, const std::shared_ptr<tree<t_A>> &t2) const {
      return std::visit(
          Overloaded{
              [&](const typename tree<t_A>::Leaf _args)
                  -> std::shared_ptr<tree<t_A>> {
                return std::visit(
                    Overloaded{[](const typename tree<t_A>::Leaf _args)
                                   -> std::shared_ptr<tree<t_A>> {
                                 return tree<t_A>::ctor::Leaf_();
                               },
                               [](const typename tree<t_A>::Node _args)
                                   -> std::shared_ptr<tree<t_A>> {
                                 t_A a = _args.d_a1;
                                 return tree<t_A>::ctor::Node_(
                                     tree<t_A>::ctor::Leaf_(), a,
                                     tree<t_A>::ctor::Leaf_());
                               }},
                    t2->v());
              },
              [&](const typename tree<t_A>::Node _args)
                  -> std::shared_ptr<tree<t_A>> {
                std::shared_ptr<tree<t_A>> l1 = _args.d_a0;
                t_A a1 = _args.d_a1;
                std::shared_ptr<tree<t_A>> r1 = _args.d_a2;
                return std::visit(
                    Overloaded{
                        [&](const typename tree<t_A>::Leaf _args)
                            -> std::shared_ptr<tree<t_A>> {
                          return tree<t_A>::ctor::Node_(
                              tree<t_A>::ctor::Leaf_(), a1,
                              tree<t_A>::ctor::Leaf_());
                        },
                        [&](const typename tree<t_A>::Node _args)
                            -> std::shared_ptr<tree<t_A>> {
                          std::shared_ptr<tree<t_A>> l2 = _args.d_a0;
                          t_A a2 = _args.d_a1;
                          std::shared_ptr<tree<t_A>> r2 = _args.d_a2;
                          return tree<t_A>::ctor::Node_(
                              std::move(l1)->merge(combine, std::move(l2)),
                              combine(a1, a2),
                              std::move(r1)->merge(combine, std::move(r2)));
                        }},
                    t2->v());
              }},
          this->v());
    }
  };

  static inline const std::shared_ptr<tree<std::shared_ptr<Nat>>> tree1 =
      tree<std::shared_ptr<Nat>>::ctor::Node_(
          tree<std::shared_ptr<Nat>>::ctor::Node_(
              tree<std::shared_ptr<Nat>>::ctor::Leaf_(),
              Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_()))),
              tree<std::shared_ptr<Nat>>::ctor::Node_(
                  tree<std::shared_ptr<Nat>>::ctor::Leaf_(),
                  Nat::ctor::S_(
                      Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(
                          Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_()))))))),
                  tree<std::shared_ptr<Nat>>::ctor::Leaf_())),
          Nat::ctor::S_(Nat::ctor::O_()),
          tree<std::shared_ptr<Nat>>::ctor::Node_(
              tree<std::shared_ptr<Nat>>::ctor::Leaf_(),
              Nat::ctor::S_(
                  Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_())))),
              tree<std::shared_ptr<Nat>>::ctor::Node_(
                  tree<std::shared_ptr<Nat>>::ctor::Node_(
                      tree<std::shared_ptr<Nat>>::ctor::Leaf_(),
                      Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(
                          Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_())))))),
                      tree<std::shared_ptr<Nat>>::ctor::Leaf_()),
                  Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_())),
                  tree<std::shared_ptr<Nat>>::ctor::Leaf_())));
};

#endif // INCLUDED_TREE
