#include "lazy.h"
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

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
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
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
  template <typename T1, MapsTo<T1, A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> std::shared_ptr<List<T1>> {
              return List<T1>::ctor::nil_();
            },
            [&](const typename List<A>::cons _args)
                -> std::shared_ptr<List<T1>> {
              A a = _args._a0;
              std::shared_ptr<List<A>> l0 = _args._a1;
              return List<T1>::ctor::cons_(f(a),
                                           std::move(l0)->template map<T1>(f));
            }},
        this->v());
  }
};

struct Cotree {
  template <typename A> struct colist {
  public:
    struct conil {};
    struct cocons {
      A _a0;
      std::shared_ptr<colist<A>> _a1;
    };
    using variant_t = std::variant<conil, cocons>;

  private:
    crane::lazy<variant_t> lazy_v_;
    explicit colist(conil _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}
    explicit colist(cocons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}
    explicit colist(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<colist<A>> conil_() {
        return std::shared_ptr<colist<A>>(new colist<A>(conil{}));
      }
      static std::shared_ptr<colist<A>>
      cocons_(A a0, const std::shared_ptr<colist<A>> &a1) {
        return std::shared_ptr<colist<A>>(new colist<A>(cocons{a0, a1}));
      }
      static std::unique_ptr<colist<A>> conil_uptr() {
        return std::unique_ptr<colist<A>>(new colist<A>(conil{}));
      }
      static std::unique_ptr<colist<A>>
      cocons_uptr(A a0, const std::shared_ptr<colist<A>> &a1) {
        return std::unique_ptr<colist<A>>(new colist<A>(cocons{a0, a1}));
      }
      static std::shared_ptr<colist<A>>
      lazy_(std::function<std::shared_ptr<colist<A>>()> thunk) {
        return std::shared_ptr<colist<A>>(
            new colist<A>(std::function<variant_t()>([=](void) -> variant_t {
              std::shared_ptr<colist<A>> _tmp = thunk();
              return std::move(const_cast<variant_t &>(_tmp->v()));
            })));
      }
    };
    const variant_t &v() const { return lazy_v_.force(); }
  };

  template <typename A> struct cotree {
  public:
    struct conode {
      A _a0;
      std::shared_ptr<colist<std::shared_ptr<cotree<A>>>> _a1;
    };
    using variant_t = std::variant<conode>;

  private:
    crane::lazy<variant_t> lazy_v_;
    explicit cotree(conode _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}
    explicit cotree(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<cotree<A>>
      conode_(A a0,
              const std::shared_ptr<colist<std::shared_ptr<cotree<A>>>> &a1) {
        return std::shared_ptr<cotree<A>>(new cotree<A>(conode{a0, a1}));
      }
      static std::unique_ptr<cotree<A>> conode_uptr(
          A a0, const std::shared_ptr<colist<std::shared_ptr<cotree<A>>>> &a1) {
        return std::unique_ptr<cotree<A>>(new cotree<A>(conode{a0, a1}));
      }
      static std::shared_ptr<cotree<A>>
      lazy_(std::function<std::shared_ptr<cotree<A>>()> thunk) {
        return std::shared_ptr<cotree<A>>(
            new cotree<A>(std::function<variant_t()>([=](void) -> variant_t {
              std::shared_ptr<cotree<A>> _tmp = thunk();
              return std::move(const_cast<variant_t &>(_tmp->v()));
            })));
      }
    };
    const variant_t &v() const { return lazy_v_.force(); }
    A root() const {
      return std::visit(
          Overloaded{[](const typename cotree<A>::conode _args) -> A {
            A a = _args._a0;
            return a;
          }},
          this->v());
    }
    std::shared_ptr<colist<std::shared_ptr<cotree<A>>>> children() const {
      return colist<std::shared_ptr<cotree<A>>>::ctor::lazy_(
          [=](void) -> std::shared_ptr<colist<std::shared_ptr<cotree<A>>>> {
            return std::visit(
                Overloaded{
                    [](const typename cotree<A>::conode _args)
                        -> std::shared_ptr<colist<std::shared_ptr<cotree<A>>>> {
                      std::shared_ptr<colist<std::shared_ptr<cotree<A>>>> f =
                          _args._a1;
                      return f;
                    }},
                this->v());
          });
    }
    template <typename T1, MapsTo<T1, A> F0>
    std::shared_ptr<cotree<T1>> comap_cotree(F0 &&g) const {
      return cotree<T1>::ctor::lazy_([=](void) -> std::shared_ptr<cotree<T1>> {
        return std::visit(
            Overloaded{[&](const typename cotree<A>::conode _args)
                           -> std::shared_ptr<cotree<T1>> {
              A a = _args._a0;
              std::shared_ptr<colist<std::shared_ptr<cotree<A>>>> f = _args._a1;
              return cotree<T1>::ctor::conode_(
                  g(a), comap<std::shared_ptr<cotree<A>>,
                              std::shared_ptr<cotree<T1>>>(
                            [&](const std::shared_ptr<cotree<A>> _x0)
                                -> std::shared_ptr<cotree<T1>> {
                              return _x0->template comap_cotree<T1>(g);
                            },
                            f));
            }},
            this->v());
      });
    }
    std::shared_ptr<tree<A>> tree_of_cotree(const unsigned int fuel) const {
      return std::visit(
          Overloaded{[&](const typename cotree<A>::conode _args)
                         -> std::shared_ptr<tree<A>> {
            A a = _args._a0;
            std::shared_ptr<colist<std::shared_ptr<cotree<A>>>> f = _args._a1;
            if (fuel <= 0) {
              return tree<A>::ctor::node_(
                  a, List<std::shared_ptr<tree<A>>>::ctor::nil_());
            } else {
              unsigned int fuel_ = fuel - 1;
              return tree<A>::ctor::node_(
                  a, list_of_colist<std::shared_ptr<cotree<A>>>(fuel, f)
                         ->template map<std::shared_ptr<tree<A>>>(
                             [&](const std::shared_ptr<cotree<A>> _x0)
                                 -> std::shared_ptr<tree<A>> {
                               return _x0->tree_of_cotree(fuel_);
                             }));
            }
          }},
          this->v());
    }
  };

  template <typename A> struct tree {
  public:
    struct node {
      A _a0;
      std::shared_ptr<List<std::shared_ptr<tree<A>>>> _a1;
    };
    using variant_t = std::variant<node>;

  private:
    variant_t v_;
    explicit tree(node _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<tree<A>>
      node_(A a0, const std::shared_ptr<List<std::shared_ptr<tree<A>>>> &a1) {
        return std::shared_ptr<tree<A>>(new tree<A>(node{a0, a1}));
      }
      static std::unique_ptr<tree<A>>
      node_uptr(A a0,
                const std::shared_ptr<List<std::shared_ptr<tree<A>>>> &a1) {
        return std::unique_ptr<tree<A>>(new tree<A>(node{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<List<std::shared_ptr<tree<T1>>>>> F0>
  static T2 tree_rect(F0 &&f, const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T1>::node _args) -> T2 {
          T1 a = _args._a0;
          std::shared_ptr<List<std::shared_ptr<tree<T1>>>> l = _args._a1;
          return f(a, std::move(l));
        }},
        t->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<List<std::shared_ptr<tree<T1>>>>> F0>
  static T2 tree_rec(F0 &&f, const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T1>::node _args) -> T2 {
          T1 a = _args._a0;
          std::shared_ptr<List<std::shared_ptr<tree<T1>>>> l = _args._a1;
          return f(a, std::move(l));
        }},
        t->v());
  }

  template <typename T1>
  static T1 tree_root(const std::shared_ptr<tree<T1>> &t) {
    return std::visit(Overloaded{[](const typename tree<T1>::node _args) -> T1 {
                        T1 a = _args._a0;
                        return a;
                      }},
                      t->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<colist<T2>>
  comap(F0 &&f, const std::shared_ptr<colist<T1>> &l) {
    return colist<T2>::ctor::lazy_([=](void) -> std::shared_ptr<colist<T2>> {
      return std::visit(Overloaded{[](const typename colist<T1>::conil _args)
                                       -> std::shared_ptr<colist<T2>> {
                                     return colist<T2>::ctor::conil_();
                                   },
                                   [&](const typename colist<T1>::cocons _args)
                                       -> std::shared_ptr<colist<T2>> {
                                     T1 x = _args._a0;
                                     std::shared_ptr<colist<T1>> xs = _args._a1;
                                     return colist<T2>::ctor::cocons_(
                                         f(x), comap<T1, T2>(f, xs));
                                   }},
                        l->v());
    });
  }

  template <typename T1>
  static std::shared_ptr<cotree<T1>> singleton_cotree(const T1 a) {
    return cotree<T1>::ctor::lazy_([=](void) -> std::shared_ptr<cotree<T1>> {
      return cotree<T1>::ctor::conode_(
          a, colist<std::shared_ptr<cotree<T1>>>::ctor::conil_());
    });
  }

  template <typename T1, MapsTo<std::shared_ptr<colist<T1>>, T1> F0>
  static std::shared_ptr<cotree<T1>> unfold_cotree(F0 &&next, const T1 init) {
    return cotree<T1>::ctor::lazy_([=](void) -> std::shared_ptr<cotree<T1>> {
      return cotree<T1>::ctor::conode_(
          init, comap<T1, std::shared_ptr<cotree<T1>>>(
                    [&](const T1 _x0) -> std::shared_ptr<cotree<T1>> {
                      return unfold_cotree<T1>(next, _x0);
                    },
                    next(init)));
    });
  }

  template <typename T1>
  static std::shared_ptr<List<T1>>
  list_of_colist(const unsigned int fuel,
                 const std::shared_ptr<colist<T1>> &l) {
    if (fuel <= 0) {
      return List<T1>::ctor::nil_();
    } else {
      unsigned int fuel_ = fuel - 1;
      return std::visit(Overloaded{[](const typename colist<T1>::conil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::nil_();
                                   },
                                   [&](const typename colist<T1>::cocons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     T1 x = _args._a0;
                                     std::shared_ptr<colist<T1>> xs = _args._a1;
                                     return List<T1>::ctor::cons_(
                                         x, list_of_colist<T1>(fuel_, xs));
                                   }},
                        l->v());
    }
  }

  template <typename T1>
  static unsigned int tree_size(const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[](const typename tree<T1>::node _args) -> unsigned int {
          std::shared_ptr<List<std::shared_ptr<tree<T1>>>> cs = _args._a1;
          return ([&](void) {
            std::function<unsigned int(
                std::shared_ptr<List<std::shared_ptr<tree<T1>>>>)>
                aux;
            aux = [&](std::shared_ptr<List<std::shared_ptr<tree<T1>>>> l)
                -> unsigned int {
              return std::visit(
                  Overloaded{
                      [](const typename List<std::shared_ptr<tree<T1>>>::nil
                             _args) -> unsigned int { return 0u; },
                      [&](const typename List<std::shared_ptr<tree<T1>>>::cons
                              _args) -> unsigned int {
                        std::shared_ptr<tree<T1>> t_ = _args._a0;
                        std::shared_ptr<List<std::shared_ptr<tree<T1>>>> rest =
                            _args._a1;
                        return (tree_size<T1>(std::move(t_)) +
                                aux(std::move(rest)));
                      }},
                  l->v());
            };
            return aux(cs);
          }() + 1);
        }},
        t->v());
  }

  static inline const std::shared_ptr<cotree<unsigned int>> sample_cotree =
      cotree<unsigned int>::ctor::conode_(
          1u,
          colist<std::shared_ptr<cotree<unsigned int>>>::ctor::cocons_(
              singleton_cotree<unsigned int>(2u),
              colist<std::shared_ptr<cotree<unsigned int>>>::ctor::cocons_(
                  singleton_cotree<unsigned int>(3u),
                  colist<
                      std::shared_ptr<cotree<unsigned int>>>::ctor::conil_())));

  static inline const unsigned int test_root = sample_cotree->root();

  static inline const unsigned int test_doubled_root =
      sample_cotree
          ->template comap_cotree<unsigned int>(
              [](unsigned int n) { return (n * 2u); })
          ->root();

  static std::shared_ptr<colist<unsigned int>> nats(const unsigned int n);

  static inline const std::shared_ptr<List<unsigned int>> test_first_five =
      list_of_colist<unsigned int>(5u, nats(0u));

  static std::shared_ptr<colist<unsigned int>>
  binary_children(const unsigned int n);

  static inline const std::shared_ptr<cotree<unsigned int>> binary_tree =
      unfold_cotree<unsigned int>(binary_children, 0u);

  static inline const unsigned int test_binary_root = binary_tree->root();

  static inline const std::shared_ptr<tree<unsigned int>> test_approx =
      binary_tree->tree_of_cotree(2u);

  static inline const unsigned int test_approx_root =
      tree_root<unsigned int>(test_approx);

  static inline const unsigned int test_approx_size =
      tree_size<unsigned int>(test_approx);
};
