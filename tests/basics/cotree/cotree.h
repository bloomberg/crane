#ifndef INCLUDED_COTREE
#define INCLUDED_COTREE

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

  template <typename T1, MapsTo<T1, t_A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<t_A>::Nil _args)
                -> std::shared_ptr<List<T1>> { return List<T1>::ctor::Nil_(); },
            [&](const typename List<t_A>::Cons _args)
                -> std::shared_ptr<List<T1>> {
              t_A a = _args.d_a0;
              std::shared_ptr<List<t_A>> l0 = _args.d_a1;
              return List<T1>::ctor::Cons_(f(a),
                                           std::move(l0)->template map<T1>(f));
            }},
        this->v());
  }
};

struct Cotree {
  template <typename t_A> struct colist {
    // TYPES
    struct Conil {};

    struct Cocons {
      t_A d_a0;
      std::shared_ptr<colist<t_A>> d_a1;
    };

    using variant_t = std::variant<Conil, Cocons>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

    // CREATORS
    explicit colist(Conil _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(Cocons _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<colist<t_A>> Conil_() {
        return std::shared_ptr<colist<t_A>>(new colist<t_A>(Conil{}));
      }

      static std::shared_ptr<colist<t_A>>
      Cocons_(t_A a0, const std::shared_ptr<colist<t_A>> &a1) {
        return std::shared_ptr<colist<t_A>>(new colist<t_A>(Cocons{a0, a1}));
      }

      static std::unique_ptr<colist<t_A>> Conil_uptr() {
        return std::unique_ptr<colist<t_A>>(new colist<t_A>(Conil{}));
      }

      static std::unique_ptr<colist<t_A>>
      Cocons_uptr(t_A a0, const std::shared_ptr<colist<t_A>> &a1) {
        return std::unique_ptr<colist<t_A>>(new colist<t_A>(Cocons{a0, a1}));
      }

      static std::shared_ptr<colist<t_A>>
      lazy_(std::function<std::shared_ptr<colist<t_A>>()> thunk) {
        return std::shared_ptr<colist<t_A>>(new colist<t_A>(
            std::function<variant_t()>([=](void) mutable -> variant_t {
              std::shared_ptr<colist<t_A>> _tmp = thunk();
              return _tmp->v();
            })));
      }
    };

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }
  };

  template <typename t_A> struct cotree {
    // TYPES
    struct Conode {
      t_A d_a0;
      std::shared_ptr<colist<std::shared_ptr<cotree<t_A>>>> d_a1;
    };

    using variant_t = std::variant<Conode>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

    // CREATORS
    explicit cotree(Conode _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit cotree(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<cotree<t_A>>
      Conode_(t_A a0,
              const std::shared_ptr<colist<std::shared_ptr<cotree<t_A>>>> &a1) {
        return std::shared_ptr<cotree<t_A>>(new cotree<t_A>(Conode{a0, a1}));
      }

      static std::unique_ptr<cotree<t_A>> Conode_uptr(
          t_A a0,
          const std::shared_ptr<colist<std::shared_ptr<cotree<t_A>>>> &a1) {
        return std::unique_ptr<cotree<t_A>>(new cotree<t_A>(Conode{a0, a1}));
      }

      static std::shared_ptr<cotree<t_A>>
      lazy_(std::function<std::shared_ptr<cotree<t_A>>()> thunk) {
        return std::shared_ptr<cotree<t_A>>(new cotree<t_A>(
            std::function<variant_t()>([=](void) mutable -> variant_t {
              std::shared_ptr<cotree<t_A>> _tmp = thunk();
              return _tmp->v();
            })));
      }
    };

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }

    t_A root() const {
      return std::visit(
          Overloaded{[](const typename cotree<t_A>::Conode _args) -> t_A {
            t_A a = _args.d_a0;
            return a;
          }},
          this->v());
    }

    std::shared_ptr<colist<std::shared_ptr<cotree<t_A>>>> children() const {
      return colist<std::shared_ptr<cotree<t_A>>>::ctor::lazy_(
          [=, this](
              void) -> std::shared_ptr<colist<std::shared_ptr<cotree<t_A>>>> {
            return std::visit(
                Overloaded{[](const typename cotree<t_A>::Conode _args)
                               -> std::shared_ptr<
                                   colist<std::shared_ptr<cotree<t_A>>>> {
                  std::shared_ptr<colist<std::shared_ptr<cotree<t_A>>>> f =
                      _args.d_a1;
                  return f;
                }},
                this->v());
          });
    }

    template <typename T1, MapsTo<T1, t_A> F0>
    std::shared_ptr<cotree<T1>> comap_cotree(F0 &&g) const {
      return cotree<T1>::ctor::lazy_(
          [=, this](void) -> std::shared_ptr<cotree<T1>> {
            return std::visit(
                Overloaded{[&](const typename cotree<t_A>::Conode _args)
                               -> std::shared_ptr<cotree<T1>> {
                  t_A a = _args.d_a0;
                  std::shared_ptr<colist<std::shared_ptr<cotree<t_A>>>> f =
                      _args.d_a1;
                  return cotree<T1>::ctor::Conode_(
                      g(a), comap<std::shared_ptr<cotree<t_A>>,
                                  std::shared_ptr<cotree<T1>>>(
                                [&](const std::shared_ptr<cotree<t_A>> &_x0)
                                    -> std::shared_ptr<cotree<T1>> {
                                  return _x0->template comap_cotree<T1>(g);
                                },
                                f));
                }},
                this->v());
          });
    }
  };

  template <typename t_A> struct tree {
    // TYPES
    struct Node {
      t_A d_a0;
      std::shared_ptr<List<std::shared_ptr<tree<t_A>>>> d_a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit tree(Node _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<tree<t_A>>
      Node_(t_A a0,
            const std::shared_ptr<List<std::shared_ptr<tree<t_A>>>> &a1) {
        return std::shared_ptr<tree<t_A>>(new tree<t_A>(Node{a0, a1}));
      }

      static std::unique_ptr<tree<t_A>>
      Node_uptr(t_A a0,
                const std::shared_ptr<List<std::shared_ptr<tree<t_A>>>> &a1) {
        return std::unique_ptr<tree<t_A>>(new tree<t_A>(Node{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<List<std::shared_ptr<tree<T1>>>>> F0>
  static T2 tree_rect(F0 &&f, const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T1>::Node _args) -> T2 {
          T1 a = _args.d_a0;
          std::shared_ptr<List<std::shared_ptr<tree<T1>>>> l = _args.d_a1;
          return f(a, std::move(l));
        }},
        t->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<List<std::shared_ptr<tree<T1>>>>> F0>
  static T2 tree_rec(F0 &&f, const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T1>::Node _args) -> T2 {
          T1 a = _args.d_a0;
          std::shared_ptr<List<std::shared_ptr<tree<T1>>>> l = _args.d_a1;
          return f(a, std::move(l));
        }},
        t->v());
  }

  template <typename T1>
  static T1 tree_root(const std::shared_ptr<tree<T1>> &t) {
    return std::visit(Overloaded{[](const typename tree<T1>::Node _args) -> T1 {
                        T1 a = _args.d_a0;
                        return a;
                      }},
                      t->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<colist<T2>>
  comap(F0 &&f, const std::shared_ptr<colist<T1>> &l) {
    return colist<T2>::ctor::lazy_(
        [=](void) mutable -> std::shared_ptr<colist<T2>> {
          return std::visit(
              Overloaded{[](const typename colist<T1>::Conil _args)
                             -> std::shared_ptr<colist<T2>> {
                           return colist<T2>::ctor::Conil_();
                         },
                         [&](const typename colist<T1>::Cocons _args)
                             -> std::shared_ptr<colist<T2>> {
                           T1 x = _args.d_a0;
                           std::shared_ptr<colist<T1>> xs = _args.d_a1;
                           return colist<T2>::ctor::Cocons_(
                               f(x), comap<T1, T2>(f, xs));
                         }},
              l->v());
        });
  }

  template <typename T1>
  static std::shared_ptr<cotree<T1>> singleton_cotree(const T1 a) {
    return cotree<T1>::ctor::lazy_(
        [=](void) mutable -> std::shared_ptr<cotree<T1>> {
          return cotree<T1>::ctor::Conode_(
              a, colist<std::shared_ptr<cotree<T1>>>::ctor::Conil_());
        });
  }

  template <typename T1, MapsTo<std::shared_ptr<colist<T1>>, T1> F0>
  static std::shared_ptr<cotree<T1>> unfold_cotree(F0 &&next, const T1 init) {
    return cotree<T1>::ctor::lazy_(
        [=](void) mutable -> std::shared_ptr<cotree<T1>> {
          return cotree<T1>::ctor::Conode_(
              init, comap<T1, std::shared_ptr<cotree<T1>>>(
                        [&](T1 _x0) -> std::shared_ptr<cotree<T1>> {
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
      return List<T1>::ctor::Nil_();
    } else {
      unsigned int fuel_ = fuel - 1;
      return std::visit(Overloaded{[](const typename colist<T1>::Conil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::Nil_();
                                   },
                                   [&](const typename colist<T1>::Cocons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     T1 x = _args.d_a0;
                                     std::shared_ptr<colist<T1>> xs =
                                         _args.d_a1;
                                     return List<T1>::ctor::Cons_(
                                         x, list_of_colist<T1>(fuel_, xs));
                                   }},
                        l->v());
    }
  }

  template <typename T1>
  static std::shared_ptr<tree<T1>>
  tree_of_cotree(const unsigned int fuel,
                 const std::shared_ptr<cotree<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename cotree<T1>::Conode _args)
                       -> std::shared_ptr<tree<T1>> {
          T1 a = _args.d_a0;
          std::shared_ptr<colist<std::shared_ptr<cotree<T1>>>> f = _args.d_a1;
          if (fuel <= 0) {
            return tree<T1>::ctor::Node_(
                a, List<std::shared_ptr<tree<T1>>>::ctor::Nil_());
          } else {
            unsigned int fuel_ = fuel - 1;
            return tree<T1>::ctor::Node_(
                a, list_of_colist<std::shared_ptr<cotree<T1>>>(fuel, f)
                       ->template map<std::shared_ptr<tree<T1>>>(
                           [&](const std::shared_ptr<cotree<T1>> &_x0)
                               -> std::shared_ptr<tree<T1>> {
                             return tree_of_cotree<T1>(fuel_, _x0);
                           }));
          }
        }},
        t->v());
  }

  template <typename T1>
  __attribute__((pure)) static unsigned int
  tree_size(const std::shared_ptr<tree<T1>> &t) {
    return std::visit(
        Overloaded{[](const typename tree<T1>::Node _args) -> unsigned int {
          std::shared_ptr<List<std::shared_ptr<tree<T1>>>> cs = _args.d_a1;
          return ([&](void) {
            std::function<unsigned int(
                std::shared_ptr<List<std::shared_ptr<tree<T1>>>>)>
                aux;
            aux = [&](std::shared_ptr<List<std::shared_ptr<tree<T1>>>> l)
                -> unsigned int {
              return std::visit(
                  Overloaded{
                      [](const typename List<std::shared_ptr<tree<T1>>>::Nil
                             _args) -> unsigned int { return 0u; },
                      [&](const typename List<std::shared_ptr<tree<T1>>>::Cons
                              _args) -> unsigned int {
                        std::shared_ptr<tree<T1>> t_ = _args.d_a0;
                        std::shared_ptr<List<std::shared_ptr<tree<T1>>>> rest =
                            _args.d_a1;
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
      cotree<unsigned int>::ctor::Conode_(
          1u,
          colist<std::shared_ptr<cotree<unsigned int>>>::ctor::Cocons_(
              singleton_cotree<unsigned int>(2u),
              colist<std::shared_ptr<cotree<unsigned int>>>::ctor::Cocons_(
                  singleton_cotree<unsigned int>(3u),
                  colist<
                      std::shared_ptr<cotree<unsigned int>>>::ctor::Conil_())));
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
      tree_of_cotree<unsigned int>(2u, binary_tree);
  static inline const unsigned int test_approx_root =
      tree_root<unsigned int>(test_approx);
  static inline const unsigned int test_approx_size =
      tree_size<unsigned int>(test_approx);
};

#endif // INCLUDED_COTREE
