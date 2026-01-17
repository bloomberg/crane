#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Bool0 {
  struct bool0 {
  public:
    struct true0 {};
    struct false0 {};
    using variant_t = std::variant<true0, false0>;

  private:
    variant_t v_;
    explicit bool0(true0 x) : v_(std::move(x)) {}
    explicit bool0(false0 x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<bool0> true0_() {
        return std::shared_ptr<bool0>(new bool0(true0{}));
      }
      static std::shared_ptr<bool0> false0_() {
        return std::shared_ptr<bool0>(new bool0(false0{}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct Nat {
  struct nat {
  public:
    struct O {};
    struct S {
      std::shared_ptr<nat> _a0;
    };
    using variant_t = std::variant<O, S>;

  private:
    variant_t v_;
    explicit nat(O x) : v_(std::move(x)) {}
    explicit nat(S x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<nat> O_() {
        return std::shared_ptr<nat>(new nat(O{}));
      }
      static std::shared_ptr<nat> S_(const std::shared_ptr<nat> &a0) {
        return std::shared_ptr<nat>(new nat(S{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct List {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil x) : v_(std::move(x)) {}
    explicit list(cons x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<list<A>> nil_() {
        return std::shared_ptr<list<A>>(new list<A>(nil{}));
      }
      static std::shared_ptr<list<A>>
      cons_(A a0, const std::shared_ptr<list<A>> &a1) {
        return std::shared_ptr<list<A>>(new list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    std::shared_ptr<list<A>> app(const std::shared_ptr<list<A>> &m) const {
      return std::visit(
          Overloaded{[&](const typename List::list<A>::nil _args)
                         -> std::shared_ptr<List::list<A>> { return m; },
                     [&](const typename List::list<A>::cons _args)
                         -> std::shared_ptr<List::list<A>> {
                       A a = _args._a0;
                       std::shared_ptr<List::list<A>> l1 = _args._a1;
                       return List::list<A>::ctor::cons_(a, l1->app(m));
                     }},
          this->v());
    }
  };
};

std::shared_ptr<Nat::nat> add(const std::shared_ptr<Nat::nat> &n,
                              const std::shared_ptr<Nat::nat> &m);

std::shared_ptr<Nat::nat> max(const std::shared_ptr<Nat::nat> &n,
                              const std::shared_ptr<Nat::nat> &m);

struct Tree {
  template <typename A> struct tree {
  public:
    struct leaf {};
    struct node {
      std::shared_ptr<tree<A>> _a0;
      A _a1;
      std::shared_ptr<tree<A>> _a2;
    };
    using variant_t = std::variant<leaf, node>;

  private:
    variant_t v_;
    explicit tree(leaf x) : v_(std::move(x)) {}
    explicit tree(node x) : v_(std::move(x)) {}

  public:
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
    };
    const variant_t &v() const { return v_; }
    template <MapsTo<A, A, A> F0>
    std::shared_ptr<tree<A>> merge(F0 &&combine,
                                   const std::shared_ptr<tree<A>> &t2) const {
      return std::visit(
          Overloaded{[&](const typename tree<A>::leaf _args)
                         -> std::shared_ptr<tree<A>> {
                       return std::visit(
                           Overloaded{[&](const typename tree<A>::leaf _args)
                                          -> std::shared_ptr<tree<A>> {
                                        return tree<A>::ctor::leaf_();
                                      },
                                      [&](const typename tree<A>::node _args)
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
                           Overloaded{[&](const typename tree<A>::leaf _args)
                                          -> std::shared_ptr<tree<A>> {
                                        return tree<A>::ctor::node_(
                                            tree<A>::ctor::leaf_(), a1,
                                            tree<A>::ctor::leaf_());
                                      },
                                      [&](const typename tree<A>::node _args)
                                          -> std::shared_ptr<tree<A>> {
                                        std::shared_ptr<tree<A>> l2 = _args._a0;
                                        A a2 = _args._a1;
                                        std::shared_ptr<tree<A>> r2 = _args._a2;
                                        return tree<A>::ctor::node_(
                                            l1->merge(combine, l2),
                                            combine(a1, a2),
                                            r1->merge(combine, r2));
                                      }},
                           t2->v());
                     }},
          this->v());
    }
    std::shared_ptr<List::list<A>> flatten() const {
      return std::visit(
          Overloaded{[&](const typename tree<A>::leaf _args)
                         -> std::shared_ptr<List::list<A>> {
                       return List::list<A>::ctor::nil_();
                     },
                     [&](const typename tree<A>::node _args)
                         -> std::shared_ptr<List::list<A>> {
                       std::shared_ptr<tree<A>> l = _args._a0;
                       A x = _args._a1;
                       std::shared_ptr<tree<A>> r = _args._a2;
                       return l->flatten()->app(
                           List::list<A>::ctor::cons_(x, r->flatten()));
                     }},
          this->v());
    }
    std::shared_ptr<Nat::nat> height() const {
      return std::visit(
          Overloaded{[&](const typename tree<A>::leaf _args)
                         -> std::shared_ptr<Nat::nat> {
                       return Nat::nat::ctor::S_(Nat::nat::ctor::O_());
                     },
                     [&](const typename tree<A>::node _args)
                         -> std::shared_ptr<Nat::nat> {
                       std::shared_ptr<tree<A>> l = _args._a0;
                       std::shared_ptr<tree<A>> r = _args._a2;
                       return add(Nat::nat::ctor::S_(Nat::nat::ctor::O_()),
                                  max(l->height(), r->height()));
                     }},
          this->v());
    }
    std::shared_ptr<Nat::nat> size() const {
      return std::visit(
          Overloaded{[&](const typename tree<A>::leaf _args)
                         -> std::shared_ptr<Nat::nat> {
                       return Nat::nat::ctor::S_(Nat::nat::ctor::O_());
                     },
                     [&](const typename tree<A>::node _args)
                         -> std::shared_ptr<Nat::nat> {
                       std::shared_ptr<tree<A>> l = _args._a0;
                       std::shared_ptr<tree<A>> r = _args._a2;
                       return add(add(Nat::nat::ctor::S_(Nat::nat::ctor::O_()),
                                      l->size()),
                                  r->size());
                     }},
          this->v());
    }
    std::shared_ptr<Bool0::bool0> is_leaf() const {
      return std::visit(Overloaded{[&](const typename tree<A>::leaf _args)
                                       -> std::shared_ptr<Bool0::bool0> {
                                     return Bool0::bool0::ctor::true0_();
                                   },
                                   [&](const typename tree<A>::node _args)
                                       -> std::shared_ptr<Bool0::bool0> {
                                     return Bool0::bool0::ctor::false0_();
                                   }},
                        this->v());
    }
    template <typename T2, MapsTo<T2, std::shared_ptr<tree<A>>, T2, A,
                                  std::shared_ptr<tree<A>>, T2>
                               F1>
    T2 tree_rec(const T2 f, F1 &&f0) const {
      return std::visit(
          Overloaded{
              [&](const typename tree<A>::leaf _args) -> T2 { return f; },
              [&](const typename tree<A>::node _args) -> T2 {
                std::shared_ptr<tree<A>> t0 = _args._a0;
                A y = _args._a1;
                std::shared_ptr<tree<A>> t1 = _args._a2;
                return f0(t0, t0->tree_rec(f, f0), y, t1, t1->tree_rec(f, f0));
              }},
          this->v());
    }
    template <typename T2, MapsTo<T2, std::shared_ptr<tree<A>>, T2, A,
                                  std::shared_ptr<tree<A>>, T2>
                               F1>
    T2 tree_rect(const T2 f, F1 &&f0) const {
      return std::visit(
          Overloaded{
              [&](const typename tree<A>::leaf _args) -> T2 { return f; },
              [&](const typename tree<A>::node _args) -> T2 {
                std::shared_ptr<tree<A>> t0 = _args._a0;
                A y = _args._a1;
                std::shared_ptr<tree<A>> t1 = _args._a2;
                return f0(t0, t0->tree_rect(f, f0), y, t1,
                          t1->tree_rect(f, f0));
              }},
          this->v());
    }
  };

  static inline const std::shared_ptr<tree<std::shared_ptr<Nat::nat>>> tree1 =
      tree<std::shared_ptr<Nat::nat>>::ctor::node_(
          tree<std::shared_ptr<Nat::nat>>::ctor::node_(
              tree<std::shared_ptr<Nat::nat>>::ctor::leaf_(),
              Nat::nat::ctor::S_(
                  Nat::nat::ctor::S_(Nat::nat::ctor::S_(Nat::nat::ctor::O_()))),
              tree<std::shared_ptr<Nat::nat>>::ctor::node_(
                  tree<std::shared_ptr<Nat::nat>>::ctor::leaf_(),
                  Nat::nat::ctor::S_(Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                      Nat::nat::ctor::S_(Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                          Nat::nat::ctor::S_(Nat::nat::ctor::O_()))))))),
                  tree<std::shared_ptr<Nat::nat>>::ctor::leaf_())),
          Nat::nat::ctor::S_(Nat::nat::ctor::O_()),
          tree<std::shared_ptr<Nat::nat>>::ctor::node_(
              tree<std::shared_ptr<Nat::nat>>::ctor::leaf_(),
              Nat::nat::ctor::S_(Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                  Nat::nat::ctor::S_(Nat::nat::ctor::O_())))),
              tree<std::shared_ptr<Nat::nat>>::ctor::node_(
                  tree<std::shared_ptr<Nat::nat>>::ctor::node_(
                      tree<std::shared_ptr<Nat::nat>>::ctor::leaf_(),
                      Nat::nat::ctor::S_(Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                          Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                              Nat::nat::ctor::S_(Nat::nat::ctor::O_())))))),
                      tree<std::shared_ptr<Nat::nat>>::ctor::leaf_()),
                  Nat::nat::ctor::S_(Nat::nat::ctor::S_(Nat::nat::ctor::O_())),
                  tree<std::shared_ptr<Nat::nat>>::ctor::leaf_())));
};
