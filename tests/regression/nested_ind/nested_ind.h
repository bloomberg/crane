#ifndef INCLUDED_NESTED_IND
#define INCLUDED_NESTED_IND

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
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

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    return std::visit(
        Overloaded{[&](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<t_A>> { return m; },
                   [&](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<t_A>> {
                     return List<t_A>::ctor::Cons_(_args.d_a0,
                                                   _args.d_a1->app(m));
                   }},
        this->v());
  }
};

struct NestedInd {
  template <typename t_A> struct custom_list {
    // TYPES
    struct Cnil {};

    struct Ccons {
      t_A d_a0;
      std::shared_ptr<custom_list<t_A>> d_a1;
    };

    using variant_t = std::variant<Cnil, Ccons>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit custom_list(Cnil _v) : d_v_(std::move(_v)) {}

    explicit custom_list(Ccons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<custom_list<t_A>> Cnil_() {
        return std::shared_ptr<custom_list<t_A>>(new custom_list<t_A>(Cnil{}));
      }

      static std::shared_ptr<custom_list<t_A>>
      Ccons_(t_A a0, const std::shared_ptr<custom_list<t_A>> &a1) {
        return std::shared_ptr<custom_list<t_A>>(
            new custom_list<t_A>(Ccons{a0, a1}));
      }

      static std::unique_ptr<custom_list<t_A>> Cnil_uptr() {
        return std::unique_ptr<custom_list<t_A>>(new custom_list<t_A>(Cnil{}));
      }

      static std::unique_ptr<custom_list<t_A>>
      Ccons_uptr(t_A a0, const std::shared_ptr<custom_list<t_A>> &a1) {
        return std::unique_ptr<custom_list<t_A>>(
            new custom_list<t_A>(Ccons{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int custom_list_length() const {
      return std::visit(
          Overloaded{
              [](const typename custom_list<t_A>::Cnil _args) -> unsigned int {
                return 0u;
              },
              [](const typename custom_list<t_A>::Ccons _args) -> unsigned int {
                return (1u + _args.d_a1->custom_list_length());
              }},
          this->v());
    }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<custom_list<T1>>, T2> F1>
  static T2 custom_list_rect(const T2 f, F1 &&f0,
                             const std::shared_ptr<custom_list<T1>> &c) {
    return std::visit(
        Overloaded{
            [&](const typename custom_list<T1>::Cnil _args) -> T2 { return f; },
            [&](const typename custom_list<T1>::Ccons _args) -> T2 {
              return f0(_args.d_a0, _args.d_a1,
                        custom_list_rect<T1, T2>(f, f0, _args.d_a1));
            }},
        c->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<custom_list<T1>>, T2> F1>
  static T2 custom_list_rec(const T2 f, F1 &&f0,
                            const std::shared_ptr<custom_list<T1>> &c) {
    return std::visit(
        Overloaded{
            [&](const typename custom_list<T1>::Cnil _args) -> T2 { return f; },
            [&](const typename custom_list<T1>::Ccons _args) -> T2 {
              return f0(_args.d_a0, _args.d_a1,
                        custom_list_rec<T1, T2>(f, f0, _args.d_a1));
            }},
        c->v());
  }

  template <typename t_A> struct rose {
    // TYPES
    struct Node {
      t_A d_a0;
      std::shared_ptr<custom_list<std::shared_ptr<rose<t_A>>>> d_a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit rose(Node _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<rose<t_A>> Node_(
          t_A a0,
          const std::shared_ptr<custom_list<std::shared_ptr<rose<t_A>>>> &a1) {
        return std::shared_ptr<rose<t_A>>(new rose<t_A>(Node{a0, a1}));
      }

      static std::unique_ptr<rose<t_A>> Node_uptr(
          t_A a0,
          const std::shared_ptr<custom_list<std::shared_ptr<rose<t_A>>>> &a1) {
        return std::unique_ptr<rose<t_A>>(new rose<t_A>(Node{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int children_count() const {
      return std::visit(
          Overloaded{[](const typename rose<t_A>::Node _args) -> unsigned int {
            return _args.d_a1->custom_list_length();
          }},
          this->v());
    }

    t_A root() const {
      return std::visit(
          Overloaded{[](const typename rose<t_A>::Node _args) -> t_A {
            return _args.d_a0;
          }},
          this->v());
    }

    template <typename T1,
              MapsTo<T1, t_A,
                     std::shared_ptr<custom_list<std::shared_ptr<rose<t_A>>>>>
                  F0>
    T1 rose_rec(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename rose<t_A>::Node _args) -> T1 {
            return f(_args.d_a0, _args.d_a1);
          }},
          this->v());
    }

    template <typename T1,
              MapsTo<T1, t_A,
                     std::shared_ptr<custom_list<std::shared_ptr<rose<t_A>>>>>
                  F0>
    T1 rose_rect(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename rose<t_A>::Node _args) -> T1 {
            return f(_args.d_a0, _args.d_a1);
          }},
          this->v());
    }
  };

  static std::shared_ptr<rose<unsigned int>> leaf(const unsigned int n);
  static inline const std::shared_ptr<rose<unsigned int>> small_tree =
      rose<unsigned int>::ctor::Node_(
          1u,
          custom_list<std::shared_ptr<rose<unsigned int>>>::ctor::Ccons_(
              leaf(2u),
              custom_list<std::shared_ptr<rose<unsigned int>>>::ctor::Ccons_(
                  leaf(3u),
                  custom_list<
                      std::shared_ptr<rose<unsigned int>>>::ctor::Cnil_())));
  static inline const std::shared_ptr<rose<unsigned int>> bigger_tree =
      rose<unsigned int>::ctor::Node_(
          1u,
          custom_list<std::shared_ptr<rose<unsigned int>>>::ctor::Ccons_(
              small_tree,
              custom_list<std::shared_ptr<rose<unsigned int>>>::ctor::Ccons_(
                  leaf(4u),
                  custom_list<
                      std::shared_ptr<rose<unsigned int>>>::ctor::Cnil_())));
  static inline const unsigned int test_root_leaf = leaf(5u)->root();
  static inline const unsigned int test_root_small = small_tree->root();
  static inline const unsigned int test_children_leaf =
      leaf(5u)->children_count();
  static inline const unsigned int test_children_small =
      small_tree->children_count();
  static inline const unsigned int test_children_bigger =
      bigger_tree->children_count();

  struct expr {
    // TYPES
    struct Lit {
      unsigned int d_a0;
    };

    struct Add {
      std::shared_ptr<List<std::shared_ptr<expr>>> d_a0;
    };

    struct Mul {
      std::shared_ptr<List<std::shared_ptr<expr>>> d_a0;
    };

    using variant_t = std::variant<Lit, Add, Mul>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit expr(Lit _v) : d_v_(std::move(_v)) {}

    explicit expr(Add _v) : d_v_(std::move(_v)) {}

    explicit expr(Mul _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<expr> Lit_(unsigned int a0) {
        return std::shared_ptr<expr>(new expr(Lit{a0}));
      }

      static std::shared_ptr<expr>
      Add_(const std::shared_ptr<List<std::shared_ptr<expr>>> &a0) {
        return std::shared_ptr<expr>(new expr(Add{a0}));
      }

      static std::shared_ptr<expr>
      Mul_(const std::shared_ptr<List<std::shared_ptr<expr>>> &a0) {
        return std::shared_ptr<expr>(new expr(Mul{a0}));
      }

      static std::unique_ptr<expr> Lit_uptr(unsigned int a0) {
        return std::unique_ptr<expr>(new expr(Lit{a0}));
      }

      static std::unique_ptr<expr>
      Add_uptr(const std::shared_ptr<List<std::shared_ptr<expr>>> &a0) {
        return std::unique_ptr<expr>(new expr(Add{a0}));
      }

      static std::unique_ptr<expr>
      Mul_uptr(const std::shared_ptr<List<std::shared_ptr<expr>>> &a0) {
        return std::unique_ptr<expr>(new expr(Mul{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <MapsTo<unsigned int, unsigned int> F0>
    std::shared_ptr<expr> lit_map(F0 &&f) const {
      return std::visit(
          Overloaded{
              [&](const typename expr::Lit _args) -> std::shared_ptr<expr> {
                return expr::ctor::Lit_(f(_args.d_a0));
              },
              [&](const typename expr::Add _args) -> std::shared_ptr<expr> {
                return expr::ctor::Add_([&](void) {
                  std::function<std::shared_ptr<List<std::shared_ptr<expr>>>(
                      std::shared_ptr<List<std::shared_ptr<expr>>>)>
                      aux;
                  aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
                      -> std::shared_ptr<List<std::shared_ptr<expr>>> {
                    return std::visit(
                        Overloaded{
                            [](const typename List<std::shared_ptr<expr>>::Nil
                                   _args)
                                -> std::shared_ptr<
                                    List<std::shared_ptr<expr>>> {
                              return List<std::shared_ptr<expr>>::ctor::Nil_();
                            },
                            [&](const typename List<std::shared_ptr<expr>>::Cons
                                    _args)
                                -> std::shared_ptr<
                                    List<std::shared_ptr<expr>>> {
                              return List<std::shared_ptr<expr>>::ctor::Cons_(
                                  _args.d_a0->lit_map(f), aux(_args.d_a1));
                            }},
                        l->v());
                  };
                  return aux(_args.d_a0);
                }());
              },
              [&](const typename expr::Mul _args) -> std::shared_ptr<expr> {
                return expr::ctor::Mul_([&](void) {
                  std::function<std::shared_ptr<List<std::shared_ptr<expr>>>(
                      std::shared_ptr<List<std::shared_ptr<expr>>>)>
                      aux;
                  aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
                      -> std::shared_ptr<List<std::shared_ptr<expr>>> {
                    return std::visit(
                        Overloaded{
                            [](const typename List<std::shared_ptr<expr>>::Nil
                                   _args)
                                -> std::shared_ptr<
                                    List<std::shared_ptr<expr>>> {
                              return List<std::shared_ptr<expr>>::ctor::Nil_();
                            },
                            [&](const typename List<std::shared_ptr<expr>>::Cons
                                    _args)
                                -> std::shared_ptr<
                                    List<std::shared_ptr<expr>>> {
                              return List<std::shared_ptr<expr>>::ctor::Cons_(
                                  _args.d_a0->lit_map(f), aux(_args.d_a1));
                            }},
                        l->v());
                  };
                  return aux(_args.d_a0);
                }());
              }},
          this->v());
    }

    std::shared_ptr<List<unsigned int>> literals() const {
      return std::visit(
          Overloaded{
              [](const typename expr::Lit _args)
                  -> std::shared_ptr<List<unsigned int>> {
                return List<unsigned int>::ctor::Cons_(
                    _args.d_a0, List<unsigned int>::ctor::Nil_());
              },
              [](const typename expr::Add _args)
                  -> std::shared_ptr<List<unsigned int>> {
                std::function<std::shared_ptr<List<unsigned int>>(
                    std::shared_ptr<List<std::shared_ptr<expr>>>)>
                    aux;
                aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
                    -> std::shared_ptr<List<unsigned int>> {
                  return std::visit(
                      Overloaded{
                          [](const typename List<std::shared_ptr<expr>>::Nil
                                 _args0)
                              -> std::shared_ptr<List<unsigned int>> {
                            return List<unsigned int>::ctor::Nil_();
                          },
                          [&](const typename List<std::shared_ptr<expr>>::Cons
                                  _args0)
                              -> std::shared_ptr<List<unsigned int>> {
                            return _args0.d_a0->literals()->app(
                                aux(_args0.d_a1));
                          }},
                      l->v());
                };
                return aux(_args.d_a0);
              },
              [](const typename expr::Mul _args)
                  -> std::shared_ptr<List<unsigned int>> {
                std::function<std::shared_ptr<List<unsigned int>>(
                    std::shared_ptr<List<std::shared_ptr<expr>>>)>
                    aux;
                aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
                    -> std::shared_ptr<List<unsigned int>> {
                  return std::visit(
                      Overloaded{
                          [](const typename List<std::shared_ptr<expr>>::Nil
                                 _args0)
                              -> std::shared_ptr<List<unsigned int>> {
                            return List<unsigned int>::ctor::Nil_();
                          },
                          [&](const typename List<std::shared_ptr<expr>>::Cons
                                  _args0)
                              -> std::shared_ptr<List<unsigned int>> {
                            return _args0.d_a0->literals()->app(
                                aux(_args0.d_a1));
                          }},
                      l->v());
                };
                return aux(_args.d_a0);
              }},
          this->v());
    }

    __attribute__((pure)) unsigned int expr_depth() const {
      return std::visit(
          Overloaded{
              [](const typename expr::Lit _args) -> unsigned int { return 0u; },
              [](const typename expr::Add _args) -> unsigned int {
                return ([&](void) {
                  std::function<unsigned int(
                      std::shared_ptr<List<std::shared_ptr<expr>>>)>
                      aux;
                  aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
                      -> unsigned int {
                    return std::visit(
                        Overloaded{
                            [](const typename List<std::shared_ptr<expr>>::Nil
                                   _args) -> unsigned int { return 0u; },
                            [&](const typename List<std::shared_ptr<expr>>::Cons
                                    _args) -> unsigned int {
                              return std::max(_args.d_a0->expr_depth(),
                                              aux(_args.d_a1));
                            }},
                        l->v());
                  };
                  return aux(_args.d_a0);
                }() + 1);
              },
              [](const typename expr::Mul _args) -> unsigned int {
                return ([&](void) {
                  std::function<unsigned int(
                      std::shared_ptr<List<std::shared_ptr<expr>>>)>
                      aux;
                  aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
                      -> unsigned int {
                    return std::visit(
                        Overloaded{
                            [](const typename List<std::shared_ptr<expr>>::Nil
                                   _args) -> unsigned int { return 0u; },
                            [&](const typename List<std::shared_ptr<expr>>::Cons
                                    _args) -> unsigned int {
                              return std::max(_args.d_a0->expr_depth(),
                                              aux(_args.d_a1));
                            }},
                        l->v());
                  };
                  return aux(_args.d_a0);
                }() + 1);
              }},
          this->v());
    }

    __attribute__((pure)) unsigned int expr_size() const {
      return std::visit(
          Overloaded{
              [](const typename expr::Lit _args) -> unsigned int { return 1u; },
              [](const typename expr::Add _args) -> unsigned int {
                return ([&](void) {
                  std::function<unsigned int(
                      std::shared_ptr<List<std::shared_ptr<expr>>>)>
                      aux;
                  aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
                      -> unsigned int {
                    return std::visit(
                        Overloaded{
                            [](const typename List<std::shared_ptr<expr>>::Nil
                                   _args) -> unsigned int { return 0u; },
                            [&](const typename List<std::shared_ptr<expr>>::Cons
                                    _args) -> unsigned int {
                              return (_args.d_a0->expr_size() +
                                      aux(_args.d_a1));
                            }},
                        l->v());
                  };
                  return aux(_args.d_a0);
                }() + 1);
              },
              [](const typename expr::Mul _args) -> unsigned int {
                return ([&](void) {
                  std::function<unsigned int(
                      std::shared_ptr<List<std::shared_ptr<expr>>>)>
                      aux;
                  aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
                      -> unsigned int {
                    return std::visit(
                        Overloaded{
                            [](const typename List<std::shared_ptr<expr>>::Nil
                                   _args) -> unsigned int { return 0u; },
                            [&](const typename List<std::shared_ptr<expr>>::Cons
                                    _args) -> unsigned int {
                              return (_args.d_a0->expr_size() +
                                      aux(_args.d_a1));
                            }},
                        l->v());
                  };
                  return aux(_args.d_a0);
                }() + 1);
              }},
          this->v());
    }

    __attribute__((pure)) unsigned int eval() const {
      return std::visit(
          Overloaded{
              [](const typename expr::Lit _args) -> unsigned int {
                return _args.d_a0;
              },
              [](const typename expr::Add _args) -> unsigned int {
                std::function<unsigned int(
                    std::shared_ptr<List<std::shared_ptr<expr>>>)>
                    sum_all;
                sum_all = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
                    -> unsigned int {
                  return std::visit(
                      Overloaded{
                          [](const typename List<std::shared_ptr<expr>>::Nil
                                 _args0) -> unsigned int { return 0u; },
                          [&](const typename List<std::shared_ptr<expr>>::Cons
                                  _args0) -> unsigned int {
                            return (_args0.d_a0->eval() + sum_all(_args0.d_a1));
                          }},
                      l->v());
                };
                return sum_all(_args.d_a0);
              },
              [](const typename expr::Mul _args) -> unsigned int {
                std::function<unsigned int(
                    std::shared_ptr<List<std::shared_ptr<expr>>>)>
                    prod_all;
                prod_all = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
                    -> unsigned int {
                  return std::visit(
                      Overloaded{
                          [](const typename List<std::shared_ptr<expr>>::Nil
                                 _args0) -> unsigned int { return 1u; },
                          [&](const typename List<std::shared_ptr<expr>>::Cons
                                  _args0) -> unsigned int {
                            return (_args0.d_a0->eval() *
                                    prod_all(_args0.d_a1));
                          }},
                      l->v());
                };
                return prod_all(_args.d_a0);
              }},
          this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<List<std::shared_ptr<expr>>>> F1,
              MapsTo<T1, std::shared_ptr<List<std::shared_ptr<expr>>>> F2>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      return std::visit(Overloaded{[&](const typename expr::Lit _args) -> T1 {
                                     return f(_args.d_a0);
                                   },
                                   [&](const typename expr::Add _args) -> T1 {
                                     return f0(_args.d_a0);
                                   },
                                   [&](const typename expr::Mul _args) -> T1 {
                                     return f1(_args.d_a0);
                                   }},
                        this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<List<std::shared_ptr<expr>>>> F1,
              MapsTo<T1, std::shared_ptr<List<std::shared_ptr<expr>>>> F2>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      return std::visit(Overloaded{[&](const typename expr::Lit _args) -> T1 {
                                     return f(_args.d_a0);
                                   },
                                   [&](const typename expr::Add _args) -> T1 {
                                     return f0(_args.d_a0);
                                   },
                                   [&](const typename expr::Mul _args) -> T1 {
                                     return f1(_args.d_a0);
                                   }},
                        this->v());
    }
  };

  static inline const std::shared_ptr<expr> test_add =
      expr::ctor::Add_(List<std::shared_ptr<expr>>::ctor::Cons_(
          expr::ctor::Lit_(1u),
          List<std::shared_ptr<expr>>::ctor::Cons_(
              expr::ctor::Lit_(2u),
              List<std::shared_ptr<expr>>::ctor::Cons_(
                  expr::ctor::Lit_(3u),
                  List<std::shared_ptr<expr>>::ctor::Nil_()))));
  static inline const std::shared_ptr<expr> test_mul =
      expr::ctor::Mul_(List<std::shared_ptr<expr>>::ctor::Cons_(
          expr::ctor::Lit_(2u),
          List<std::shared_ptr<expr>>::ctor::Cons_(
              expr::ctor::Lit_(3u),
              List<std::shared_ptr<expr>>::ctor::Cons_(
                  expr::ctor::Lit_(4u),
                  List<std::shared_ptr<expr>>::ctor::Nil_()))));
  static inline const std::shared_ptr<expr> test_nested =
      expr::ctor::Mul_(List<std::shared_ptr<expr>>::ctor::Cons_(
          expr::ctor::Add_(List<std::shared_ptr<expr>>::ctor::Cons_(
              expr::ctor::Lit_(1u),
              List<std::shared_ptr<expr>>::ctor::Cons_(
                  expr::ctor::Lit_(2u),
                  List<std::shared_ptr<expr>>::ctor::Nil_()))),
          List<std::shared_ptr<expr>>::ctor::Cons_(
              expr::ctor::Add_(List<std::shared_ptr<expr>>::ctor::Cons_(
                  expr::ctor::Lit_(3u),
                  List<std::shared_ptr<expr>>::ctor::Cons_(
                      expr::ctor::Lit_(4u),
                      List<std::shared_ptr<expr>>::ctor::Nil_()))),
              List<std::shared_ptr<expr>>::ctor::Nil_())));
  static inline const unsigned int test_eval_add = test_add->eval();
  static inline const unsigned int test_eval_mul = test_mul->eval();
  static inline const unsigned int test_eval_nested = test_nested->eval();
  static inline const unsigned int test_size_nested = test_nested->expr_size();
  static inline const unsigned int test_depth_nested =
      test_nested->expr_depth();
  static inline const std::shared_ptr<List<unsigned int>> test_literals =
      test_nested->literals();
  static inline const unsigned int test_doubled =
      test_nested->lit_map([](unsigned int n) { return (n * 2u); })->eval();
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<
                  std::pair<
                      std::pair<
                          std::pair<
                              std::pair<
                                  std::pair<std::pair<std::pair<unsigned int,
                                                                unsigned int>,
                                                      unsigned int>,
                                            unsigned int>,
                                  unsigned int>,
                              unsigned int>,
                          unsigned int>,
                      unsigned int>,
                  unsigned int>,
              unsigned int>,
          std::shared_ptr<List<unsigned int>>>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(
                          std::make_pair(
                              std::make_pair(
                                  std::make_pair(
                                      std::make_pair(
                                          std::make_pair(
                                              std::make_pair(test_root_leaf,
                                                             test_root_small),
                                              test_children_leaf),
                                          test_children_small),
                                      test_children_bigger),
                                  test_eval_add),
                              test_eval_mul),
                          test_eval_nested),
                      test_size_nested),
                  test_depth_nested),
              test_literals),
          test_doubled);
};

#endif // INCLUDED_NESTED_IND
