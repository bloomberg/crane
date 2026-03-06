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

struct NestedIndStdlibList {
  struct expr {
  public:
    struct Lit {
      unsigned int _a0;
    };
    struct Add {
      std::shared_ptr<List<std::shared_ptr<expr>>> _a0;
    };
    struct Mul {
      std::shared_ptr<List<std::shared_ptr<expr>>> _a0;
    };
    using variant_t = std::variant<Lit, Add, Mul>;

  private:
    variant_t v_;
    explicit expr(Lit _v) : v_(std::move(_v)) {}
    explicit expr(Add _v) : v_(std::move(_v)) {}
    explicit expr(Mul _v) : v_(std::move(_v)) {}

  public:
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
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<List<std::shared_ptr<expr>>>> F1,
            MapsTo<T1, std::shared_ptr<List<std::shared_ptr<expr>>>> F2>
  static T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1,
                      const std::shared_ptr<expr> &e) {
    return std::visit(
        Overloaded{[&](const typename expr::Lit _args) -> T1 {
                     unsigned int n = _args._a0;
                     return f(std::move(n));
                   },
                   [&](const typename expr::Add _args) -> T1 {
                     std::shared_ptr<List<std::shared_ptr<expr>>> l = _args._a0;
                     return f0(std::move(l));
                   },
                   [&](const typename expr::Mul _args) -> T1 {
                     std::shared_ptr<List<std::shared_ptr<expr>>> l = _args._a0;
                     return f1(std::move(l));
                   }},
        e->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<List<std::shared_ptr<expr>>>> F1,
            MapsTo<T1, std::shared_ptr<List<std::shared_ptr<expr>>>> F2>
  static T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, const std::shared_ptr<expr> &e) {
    return std::visit(
        Overloaded{[&](const typename expr::Lit _args) -> T1 {
                     unsigned int n = _args._a0;
                     return f(std::move(n));
                   },
                   [&](const typename expr::Add _args) -> T1 {
                     std::shared_ptr<List<std::shared_ptr<expr>>> l = _args._a0;
                     return f0(std::move(l));
                   },
                   [&](const typename expr::Mul _args) -> T1 {
                     std::shared_ptr<List<std::shared_ptr<expr>>> l = _args._a0;
                     return f1(std::move(l));
                   }},
        e->v());
  }

  static unsigned int eval(const std::shared_ptr<expr> &e);

  static unsigned int expr_size(const std::shared_ptr<expr> &e);

  static unsigned int expr_depth(const std::shared_ptr<expr> &e);

  static std::shared_ptr<List<unsigned int>>
  literals(const std::shared_ptr<expr> &e);

  template <MapsTo<unsigned int, unsigned int> F0>
  static std::shared_ptr<expr> lit_map(F0 &&f, const std::shared_ptr<expr> &e) {
    return std::visit(
        Overloaded{
            [&](const typename expr::Lit _args) -> std::shared_ptr<expr> {
              unsigned int n = _args._a0;
              return expr::ctor::Lit_(f(std::move(n)));
            },
            [&](const typename expr::Add _args) -> std::shared_ptr<expr> {
              std::shared_ptr<List<std::shared_ptr<expr>>> es = _args._a0;
              return expr::ctor::Add_([&](void) {
                std::function<std::shared_ptr<List<std::shared_ptr<expr>>>(
                    std::shared_ptr<List<std::shared_ptr<expr>>>)>
                    aux;
                aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
                    -> std::shared_ptr<List<std::shared_ptr<expr>>> {
                  return std::visit(
                      Overloaded{
                          [](const typename List<std::shared_ptr<expr>>::nil
                                 _args)
                              -> std::shared_ptr<List<std::shared_ptr<expr>>> {
                            return List<std::shared_ptr<expr>>::ctor::nil_();
                          },
                          [&](const typename List<std::shared_ptr<expr>>::cons
                                  _args)
                              -> std::shared_ptr<List<std::shared_ptr<expr>>> {
                            std::shared_ptr<expr> e_ = _args._a0;
                            std::shared_ptr<List<std::shared_ptr<expr>>> rest =
                                _args._a1;
                            return List<std::shared_ptr<expr>>::ctor::cons_(
                                lit_map(f, std::move(e_)),
                                aux(std::move(rest)));
                          }},
                      l->v());
                };
                return aux(es);
              }());
            },
            [&](const typename expr::Mul _args) -> std::shared_ptr<expr> {
              std::shared_ptr<List<std::shared_ptr<expr>>> es = _args._a0;
              return expr::ctor::Mul_([&](void) {
                std::function<std::shared_ptr<List<std::shared_ptr<expr>>>(
                    std::shared_ptr<List<std::shared_ptr<expr>>>)>
                    aux;
                aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
                    -> std::shared_ptr<List<std::shared_ptr<expr>>> {
                  return std::visit(
                      Overloaded{
                          [](const typename List<std::shared_ptr<expr>>::nil
                                 _args)
                              -> std::shared_ptr<List<std::shared_ptr<expr>>> {
                            return List<std::shared_ptr<expr>>::ctor::nil_();
                          },
                          [&](const typename List<std::shared_ptr<expr>>::cons
                                  _args)
                              -> std::shared_ptr<List<std::shared_ptr<expr>>> {
                            std::shared_ptr<expr> e_ = _args._a0;
                            std::shared_ptr<List<std::shared_ptr<expr>>> rest =
                                _args._a1;
                            return List<std::shared_ptr<expr>>::ctor::cons_(
                                lit_map(f, std::move(e_)),
                                aux(std::move(rest)));
                          }},
                      l->v());
                };
                return aux(es);
              }());
            }},
        e->v());
  }

  static inline const std::shared_ptr<expr> test_add =
      expr::ctor::Add_(List<std::shared_ptr<expr>>::ctor::cons_(
          expr::ctor::Lit_((0 + 1)),
          List<std::shared_ptr<expr>>::ctor::cons_(
              expr::ctor::Lit_(((0 + 1) + 1)),
              List<std::shared_ptr<expr>>::ctor::cons_(
                  expr::ctor::Lit_((((0 + 1) + 1) + 1)),
                  List<std::shared_ptr<expr>>::ctor::nil_()))));

  static inline const std::shared_ptr<expr> test_mul =
      expr::ctor::Mul_(List<std::shared_ptr<expr>>::ctor::cons_(
          expr::ctor::Lit_(((0 + 1) + 1)),
          List<std::shared_ptr<expr>>::ctor::cons_(
              expr::ctor::Lit_((((0 + 1) + 1) + 1)),
              List<std::shared_ptr<expr>>::ctor::cons_(
                  expr::ctor::Lit_(((((0 + 1) + 1) + 1) + 1)),
                  List<std::shared_ptr<expr>>::ctor::nil_()))));

  static inline const std::shared_ptr<expr> test_nested =
      expr::ctor::Mul_(List<std::shared_ptr<expr>>::ctor::cons_(
          expr::ctor::Add_(List<std::shared_ptr<expr>>::ctor::cons_(
              expr::ctor::Lit_((0 + 1)),
              List<std::shared_ptr<expr>>::ctor::cons_(
                  expr::ctor::Lit_(((0 + 1) + 1)),
                  List<std::shared_ptr<expr>>::ctor::nil_()))),
          List<std::shared_ptr<expr>>::ctor::cons_(
              expr::ctor::Add_(List<std::shared_ptr<expr>>::ctor::cons_(
                  expr::ctor::Lit_((((0 + 1) + 1) + 1)),
                  List<std::shared_ptr<expr>>::ctor::cons_(
                      expr::ctor::Lit_(((((0 + 1) + 1) + 1) + 1)),
                      List<std::shared_ptr<expr>>::ctor::nil_()))),
              List<std::shared_ptr<expr>>::ctor::nil_())));

  static inline const unsigned int test_eval_add = eval(test_add);

  static inline const unsigned int test_eval_mul = eval(test_mul);

  static inline const unsigned int test_eval_nested = eval(test_nested);

  static inline const unsigned int test_size_nested = expr_size(test_nested);

  static inline const unsigned int test_depth_nested = expr_depth(test_nested);

  static inline const std::shared_ptr<List<unsigned int>> test_literals =
      literals(test_nested);

  static inline const unsigned int test_doubled = eval(
      lit_map([](unsigned int n) { return (n * ((0 + 1) + 1)); }, test_nested));
};
