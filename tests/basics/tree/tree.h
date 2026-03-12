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

enum class bool0 { true0, false0 };

struct Nat : public std::enable_shared_from_this<Nat> {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> _a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit Nat(O _v) : v_(std::move(_v)) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

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
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  std::shared_ptr<Nat> max(std::shared_ptr<Nat> m) const {
    return std::visit(
        Overloaded{
            [&](const typename Nat::O _args) -> std::shared_ptr<Nat> {
              return m;
            },
            [&](const typename Nat::S _args) -> std::shared_ptr<Nat> {
              std::shared_ptr<Nat> n_ = _args._a0;
              return std::visit(
                  Overloaded{
                      [&](const typename Nat::O _args) -> std::shared_ptr<Nat> {
                        return std::const_pointer_cast<Nat>(
                            this->shared_from_this());
                      },
                      [&](const typename Nat::S _args) -> std::shared_ptr<Nat> {
                        std::shared_ptr<Nat> m_ = _args._a0;
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
                     std::shared_ptr<Nat> p = _args._a0;
                     return Nat::ctor::S_(std::move(p)->add(m));
                   }},
        this->v());
  }
};

template <typename A> struct List {
  // TYPES
  struct nil {};

  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };

  using variant_t = std::variant<nil, cons>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit List(nil _v) : v_(std::move(_v)) {}

  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }

    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  std::shared_ptr<List<A>> app(std::shared_ptr<List<A>> m) const {
    return std::visit(Overloaded{[&](const typename List<A>::nil _args)
                                     -> std::shared_ptr<List<A>> { return m; },
                                 [&](const typename List<A>::cons _args)
                                     -> std::shared_ptr<List<A>> {
                                   A a = _args._a0;
                                   std::shared_ptr<List<A>> l1 = _args._a1;
                                   return List<A>::ctor::cons_(
                                       a, std::move(l1)->app(m));
                                 }},
                      this->v());
  }
};

struct Tree {
  template <typename A> struct tree {
    // TYPES
    struct leaf {};

    struct node {
      std::shared_ptr<tree<A>> _a0;
      A _a1;
      std::shared_ptr<tree<A>> _a2;
    };

    using variant_t = std::variant<leaf, node>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit tree(leaf _v) : v_(std::move(_v)) {}

    explicit tree(node _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<tree<A>> leaf_() {
        return std::shared_ptr<tree<A>>(new tree<A>(leaf{}));
      }

      static std::shared_ptr<tree<A>>
      node_(const std::shared_ptr<tree<A>> &a0, A a1,
            const std::shared_ptr<tree<A>> &a2) {
        return std::shared_ptr<tree<A>>(new tree<A>(node{a0, a1, a2}));
      }

      static std::unique_ptr<tree<A>> leaf_uptr() {
        return std::unique_ptr<tree<A>>(new tree<A>(leaf{}));
      }

      static std::unique_ptr<tree<A>>
      node_uptr(const std::shared_ptr<tree<A>> &a0, A a1,
                const std::shared_ptr<tree<A>> &a2) {
        return std::unique_ptr<tree<A>>(new tree<A>(node{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, MapsTo<T1, std::shared_ptr<tree<A>>, T1, A,
                                  std::shared_ptr<tree<A>>, T1>
                               F1>
    T1 tree_rec(const T1 f, F1 &&f0) const {
      return std::visit(
          Overloaded{
              [&](const typename tree<A>::leaf _args) -> T1 { return f; },
              [&](const typename tree<A>::node _args) -> T1 {
                std::shared_ptr<tree<A>> t0 = _args._a0;
                A y = _args._a1;
                std::shared_ptr<tree<A>> t1 = _args._a2;
                return f0(t0, t0->template tree_rec<T1>(f, f0), y, t1,
                          t1->template tree_rec<T1>(f, f0));
              }},
          this->v());
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<tree<A>>, T1, A,
                                  std::shared_ptr<tree<A>>, T1>
                               F1>
    T1 tree_rect(const T1 f, F1 &&f0) const {
      return std::visit(
          Overloaded{
              [&](const typename tree<A>::leaf _args) -> T1 { return f; },
              [&](const typename tree<A>::node _args) -> T1 {
                std::shared_ptr<tree<A>> t0 = _args._a0;
                A y = _args._a1;
                std::shared_ptr<tree<A>> t1 = _args._a2;
                return f0(t0, t0->template tree_rect<T1>(f, f0), y, t1,
                          t1->template tree_rect<T1>(f, f0));
              }},
          this->v());
    }

    bool0 is_leaf() const {
      return std::visit(
          Overloaded{[](const typename tree<A>::leaf _args) -> bool0 {
                       return bool0::true0;
                     },
                     [](const typename tree<A>::node _args) -> bool0 {
                       return bool0::false0;
                     }},
          this->v());
    }

    std::shared_ptr<Nat> size() const {
      return std::visit(
          Overloaded{
              [](const typename tree<A>::leaf _args) -> std::shared_ptr<Nat> {
                return Nat::ctor::S_(Nat::ctor::O_());
              },
              [](const typename tree<A>::node _args) -> std::shared_ptr<Nat> {
                std::shared_ptr<tree<A>> l = _args._a0;
                std::shared_ptr<tree<A>> r = _args._a2;
                return Nat::ctor::S_(Nat::ctor::O_())
                    ->add(std::move(l)->size())
                    ->add(std::move(r)->size());
              }},
          this->v());
    }

    std::shared_ptr<Nat> height() const {
      return std::visit(
          Overloaded{
              [](const typename tree<A>::leaf _args) -> std::shared_ptr<Nat> {
                return Nat::ctor::S_(Nat::ctor::O_());
              },
              [](const typename tree<A>::node _args) -> std::shared_ptr<Nat> {
                std::shared_ptr<tree<A>> l = _args._a0;
                std::shared_ptr<tree<A>> r = _args._a2;
                return Nat::ctor::S_(Nat::ctor::O_())
                    ->add(std::move(l)->height()->max(std::move(r)->height()));
              }},
          this->v());
    }

    std::shared_ptr<List<A>> flatten() const {
      return std::visit(
          Overloaded{
              [](const typename tree<A>::leaf _args)
                  -> std::shared_ptr<List<A>> { return List<A>::ctor::nil_(); },
              [](const typename tree<A>::node _args)
                  -> std::shared_ptr<List<A>> {
                std::shared_ptr<tree<A>> l = _args._a0;
                A x = _args._a1;
                std::shared_ptr<tree<A>> r = _args._a2;
                return std::move(l)->flatten()->app(
                    List<A>::ctor::cons_(x, std::move(r)->flatten()));
              }},
          this->v());
    }

    template <MapsTo<A, A, A> F0>
    std::shared_ptr<tree<A>> merge(F0 &&combine,
                                   const std::shared_ptr<tree<A>> &t2) const {
      return std::visit(
          Overloaded{
              [&](const typename tree<A>::leaf _args)
                  -> std::shared_ptr<tree<A>> {
                return std::visit(
                    Overloaded{[](const typename tree<A>::leaf _args)
                                   -> std::shared_ptr<tree<A>> {
                                 return tree<A>::ctor::leaf_();
                               },
                               [](const typename tree<A>::node _args)
                                   -> std::shared_ptr<tree<A>> {
                                 A a = _args._a1;
                                 return tree<A>::ctor::node_(
                                     tree<A>::ctor::leaf_(), a,
                                     tree<A>::ctor::leaf_());
                               }},
                    t2->v());
              },
              [&](const typename tree<A>::node _args)
                  -> std::shared_ptr<tree<A>> {
                std::shared_ptr<tree<A>> l1 = _args._a0;
                A a1 = _args._a1;
                std::shared_ptr<tree<A>> r1 = _args._a2;
                return std::visit(
                    Overloaded{
                        [&](const typename tree<A>::leaf _args)
                            -> std::shared_ptr<tree<A>> {
                          return tree<A>::ctor::node_(tree<A>::ctor::leaf_(),
                                                      a1,
                                                      tree<A>::ctor::leaf_());
                        },
                        [&](const typename tree<A>::node _args)
                            -> std::shared_ptr<tree<A>> {
                          std::shared_ptr<tree<A>> l2 = _args._a0;
                          A a2 = _args._a1;
                          std::shared_ptr<tree<A>> r2 = _args._a2;
                          return tree<A>::ctor::node_(
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
      tree<std::shared_ptr<Nat>>::ctor::node_(
          tree<std::shared_ptr<Nat>>::ctor::node_(
              tree<std::shared_ptr<Nat>>::ctor::leaf_(),
              Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_()))),
              tree<std::shared_ptr<Nat>>::ctor::node_(
                  tree<std::shared_ptr<Nat>>::ctor::leaf_(),
                  Nat::ctor::S_(
                      Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(
                          Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_()))))))),
                  tree<std::shared_ptr<Nat>>::ctor::leaf_())),
          Nat::ctor::S_(Nat::ctor::O_()),
          tree<std::shared_ptr<Nat>>::ctor::node_(
              tree<std::shared_ptr<Nat>>::ctor::leaf_(),
              Nat::ctor::S_(
                  Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_())))),
              tree<std::shared_ptr<Nat>>::ctor::node_(
                  tree<std::shared_ptr<Nat>>::ctor::node_(
                      tree<std::shared_ptr<Nat>>::ctor::leaf_(),
                      Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(
                          Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_())))))),
                      tree<std::shared_ptr<Nat>>::ctor::leaf_()),
                  Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_())),
                  tree<std::shared_ptr<Nat>>::ctor::leaf_())));
};
