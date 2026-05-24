#ifndef INCLUDED_NESTED_IND
#define INCLUDED_NESTED_IND

#include <algorithm>
#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

struct NestedInd {
  template <typename A> struct custom_list {
    // TYPES
    struct Cnil {};

    struct Ccons {
      A a0;
      std::shared_ptr<custom_list<A>> a1;
    };

    using variant_t = std::variant<Cnil, Ccons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    custom_list() {}

    explicit custom_list(Cnil _v) : v_(_v) {}

    explicit custom_list(Ccons _v) : v_(std::move(_v)) {}

    template <typename _U> explicit custom_list(const custom_list<_U> &_other) {
      if (std::holds_alternative<typename custom_list<_U>::Cnil>(_other.v())) {
        this->v_ = Cnil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename custom_list<_U>::Ccons>(_other.v());
        this->v_ = Ccons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
                        if constexpr (std::is_same_v<typename A::first_type,
                                                     std::any>)
                          return _k;
                        else
                          return std::any_cast<typename A::first_type>(_k);
                      }(),
                      [&]() -> typename A::second_type {
                        if constexpr (std::is_same_v<typename A::second_type,
                                                     std::any>)
                          return _v;
                        else
                          return std::any_cast<typename A::second_type>(_v);
                      }()};
                }
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? std::make_shared<custom_list<A>>(*a1) : nullptr};
      }
    }

    static custom_list<A> cnil() { return custom_list(Cnil{}); }

    static custom_list<A> ccons(A a0, custom_list<A> a1) {
      return custom_list(Ccons{
          std::move(a0), std::make_shared<custom_list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t custom_list_length() const {
      if (std::holds_alternative<typename custom_list<A>::Cnil>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename custom_list<A>::Ccons>(this->v());
        return (UINT64_C(1) + a1->custom_list_length());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, custom_list<A> &, T1 &>
    T1 custom_list_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename custom_list<A>::Cnil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] =
            std::get<typename custom_list<A>::Ccons>(this->v());
        return f0(a0, *a1, a1->template custom_list_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, custom_list<A> &, T1 &>
    T1 custom_list_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename custom_list<A>::Cnil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] =
            std::get<typename custom_list<A>::Ccons>(this->v());
        return f0(a0, *a1, a1->template custom_list_rect<T1>(f, f0));
      }
    }
  };

  template <typename A> struct rose {
    // TYPES
    struct Node {
      A a0;
      std::shared_ptr<custom_list<rose<A>>> a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(Node _v) : v_(std::move(_v)) {}

    template <typename _U> explicit rose(const rose<_U> &_other) {
      const auto &[a0, a1] = std::get<typename rose<_U>::Node>(_other.v());
      this->v_ = Node{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a0.type() == typeid(A))
                return std::any_cast<A>(a0);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a0);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a0);
            } else
              return A(a0);
          }(),
          a1 ? std::make_shared<NestedInd::custom_list<rose<A>>>(*a1)
             : nullptr};
    }

    static rose<A> node(A a0, custom_list<rose<A>> a1) {
      return rose(Node{std::move(a0),
                       std::make_shared<custom_list<rose<A>>>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t children_count() const {
      const auto &[a0, a1] = std::get<typename rose<A>::Node>(this->v());
      return a1->custom_list_length();
    }

    A root() const {
      const auto &[a0, a1] = std::get<typename rose<A>::Node>(this->v());
      return a0;
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, custom_list<rose<A>> &>
    T1 rose_rec(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename rose<A>::Node>(this->v());
      return f(a0, *a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, custom_list<rose<A>> &>
    T1 rose_rect(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename rose<A>::Node>(this->v());
      return f(a0, *a1);
    }
  };

  static rose<uint64_t> leaf(uint64_t n);
  static inline const rose<uint64_t> small_tree = rose<uint64_t>::node(
      UINT64_C(1),
      custom_list<rose<uint64_t>>::ccons(
          leaf(UINT64_C(2)),
          custom_list<rose<uint64_t>>::ccons(
              leaf(UINT64_C(3)), custom_list<rose<uint64_t>>::cnil())));
  static inline const rose<uint64_t> bigger_tree = rose<uint64_t>::node(
      UINT64_C(1), custom_list<rose<uint64_t>>::ccons(
                       small_tree, custom_list<rose<uint64_t>>::ccons(
                                       leaf(UINT64_C(4)),
                                       custom_list<rose<uint64_t>>::cnil())));
  static inline const uint64_t test_root_leaf = leaf(UINT64_C(5)).root();
  static inline const uint64_t test_root_small = small_tree.root();
  static inline const uint64_t test_children_leaf =
      leaf(UINT64_C(5)).children_count();
  static inline const uint64_t test_children_small =
      small_tree.children_count();
  static inline const uint64_t test_children_bigger =
      bigger_tree.children_count();

  struct expr {
    // TYPES
    struct Lit {
      uint64_t a0;
    };

    struct Add {
      std::shared_ptr<List<expr>> a0;
    };

    struct Mul {
      std::shared_ptr<List<expr>> a0;
    };

    using variant_t = std::variant<Lit, Add, Mul>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Lit _v) : v_(std::move(_v)) {}

    explicit expr(Add _v) : v_(std::move(_v)) {}

    explicit expr(Mul _v) : v_(std::move(_v)) {}

    static expr lit(uint64_t a0) { return expr(Lit{a0}); }

    static expr add(List<expr> a0) {
      return expr(Add{std::make_shared<List<expr>>(std::move(a0))});
    }

    static expr mul(List<expr> a0) {
      return expr(Mul{std::make_shared<List<expr>>(std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename F0>
      requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
    expr lit_map(F0 &&f) const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return expr::lit(f(a0));
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        return expr::add([&]() {
          auto aux_impl = [&](auto &_self_aux,
                              const List<expr> &l) -> List<expr> {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return List<expr>::nil();
            } else {
              const auto &[a1, a2] = std::get<typename List<expr>::Cons>(l.v());
              return List<expr>::cons(a1.lit_map(f), _self_aux(_self_aux, *a2));
            }
          };
          auto aux = [&](const List<expr> &l) -> List<expr> {
            return aux_impl(aux_impl, l);
          };
          return aux(*a0);
        }());
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        return expr::mul([&]() {
          auto aux_impl = [&](auto &_self_aux,
                              const List<expr> &l) -> List<expr> {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return List<expr>::nil();
            } else {
              const auto &[a1, a2] = std::get<typename List<expr>::Cons>(l.v());
              return List<expr>::cons(a1.lit_map(f), _self_aux(_self_aux, *a2));
            }
          };
          auto aux = [&](const List<expr> &l) -> List<expr> {
            return aux_impl(aux_impl, l);
          };
          return aux(*a0);
        }());
      }
    }

    List<uint64_t> literals() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return List<uint64_t>::cons(a0, List<uint64_t>::nil());
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        auto aux_impl = [](auto &_self_aux,
                           const List<expr> &l) -> List<uint64_t> {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return List<uint64_t>::nil();
          } else {
            const auto &[a00, a10] = std::get<typename List<expr>::Cons>(l.v());
            return a00.literals().app(_self_aux(_self_aux, *a10));
          }
        };
        auto aux = [&](const List<expr> &l) -> List<uint64_t> {
          return aux_impl(aux_impl, l);
        };
        return aux(*a0);
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        auto aux_impl = [](auto &_self_aux,
                           const List<expr> &l) -> List<uint64_t> {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return List<uint64_t>::nil();
          } else {
            const auto &[a00, a10] = std::get<typename List<expr>::Cons>(l.v());
            return a00.literals().app(_self_aux(_self_aux, *a10));
          }
        };
        auto aux = [&](const List<expr> &l) -> List<uint64_t> {
          return aux_impl(aux_impl, l);
        };
        return aux(*a0);
      }
    }

    uint64_t expr_depth() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        return UINT64_C(0);
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        return ([&]() {
          auto aux_impl = [](auto &_self_aux, const List<expr> &l) -> uint64_t {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return UINT64_C(0);
            } else {
              const auto &[a1, a2] = std::get<typename List<expr>::Cons>(l.v());
              return std::max(a1.expr_depth(), _self_aux(_self_aux, *a2));
            }
          };
          auto aux = [&](const List<expr> &l) -> uint64_t {
            return aux_impl(aux_impl, l);
          };
          return aux(*a0);
        }() + 1);
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        return ([&]() {
          auto aux_impl = [](auto &_self_aux, const List<expr> &l) -> uint64_t {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return UINT64_C(0);
            } else {
              const auto &[a1, a2] = std::get<typename List<expr>::Cons>(l.v());
              return std::max(a1.expr_depth(), _self_aux(_self_aux, *a2));
            }
          };
          auto aux = [&](const List<expr> &l) -> uint64_t {
            return aux_impl(aux_impl, l);
          };
          return aux(*a0);
        }() + 1);
      }
    }

    uint64_t expr_size() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        return UINT64_C(1);
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        return ([&]() {
          auto aux_impl = [](auto &_self_aux, const List<expr> &l) -> uint64_t {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return UINT64_C(0);
            } else {
              const auto &[a1, a2] = std::get<typename List<expr>::Cons>(l.v());
              return (a1.expr_size() + _self_aux(_self_aux, *a2));
            }
          };
          auto aux = [&](const List<expr> &l) -> uint64_t {
            return aux_impl(aux_impl, l);
          };
          return aux(*a0);
        }() + 1);
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        return ([&]() {
          auto aux_impl = [](auto &_self_aux, const List<expr> &l) -> uint64_t {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return UINT64_C(0);
            } else {
              const auto &[a1, a2] = std::get<typename List<expr>::Cons>(l.v());
              return (a1.expr_size() + _self_aux(_self_aux, *a2));
            }
          };
          auto aux = [&](const List<expr> &l) -> uint64_t {
            return aux_impl(aux_impl, l);
          };
          return aux(*a0);
        }() + 1);
      }
    }

    uint64_t eval() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return a0;
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        auto sum_all_impl = [](auto &_self_sum_all,
                               const List<expr> &l) -> uint64_t {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return UINT64_C(0);
          } else {
            const auto &[a00, a10] = std::get<typename List<expr>::Cons>(l.v());
            return (a00.eval() + _self_sum_all(_self_sum_all, *a10));
          }
        };
        auto sum_all = [&](const List<expr> &l) -> uint64_t {
          return sum_all_impl(sum_all_impl, l);
        };
        return sum_all(*a0);
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        auto prod_all_impl = [](auto &_self_prod_all,
                                const List<expr> &l) -> uint64_t {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return UINT64_C(1);
          } else {
            const auto &[a00, a10] = std::get<typename List<expr>::Cons>(l.v());
            return (a00.eval() * _self_prod_all(_self_prod_all, *a10));
          }
        };
        auto prod_all = [&](const List<expr> &l) -> uint64_t {
          return prod_all_impl(prod_all_impl, l);
        };
        return prod_all(*a0);
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, List<expr> &> &&
               std::is_invocable_r_v<T1, F2 &, List<expr> &>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        return f0(*a0);
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        return f1(*a0);
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, List<expr> &> &&
               std::is_invocable_r_v<T1, F2 &, List<expr> &>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        return f0(*a0);
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        return f1(*a0);
      }
    }
  };

  static inline const expr test_add = expr::add(
      List<expr>::cons(expr::lit(UINT64_C(1)),
                       List<expr>::cons(expr::lit(UINT64_C(2)),
                                        List<expr>::cons(expr::lit(UINT64_C(3)),
                                                         List<expr>::nil()))));
  static inline const expr test_mul = expr::mul(
      List<expr>::cons(expr::lit(UINT64_C(2)),
                       List<expr>::cons(expr::lit(UINT64_C(3)),
                                        List<expr>::cons(expr::lit(UINT64_C(4)),
                                                         List<expr>::nil()))));
  static inline const expr test_nested = expr::mul(List<expr>::cons(
      expr::add(List<expr>::cons(
          expr::lit(UINT64_C(1)),
          List<expr>::cons(expr::lit(UINT64_C(2)), List<expr>::nil()))),
      List<expr>::cons(
          expr::add(List<expr>::cons(
              expr::lit(UINT64_C(3)),
              List<expr>::cons(expr::lit(UINT64_C(4)), List<expr>::nil()))),
          List<expr>::nil())));
  static inline const uint64_t test_eval_add = test_add.eval();
  static inline const uint64_t test_eval_mul = test_mul.eval();
  static inline const uint64_t test_eval_nested = test_nested.eval();
  static inline const uint64_t test_size_nested = test_nested.expr_size();
  static inline const uint64_t test_depth_nested = test_nested.expr_depth();
  static inline const List<uint64_t> test_literals = test_nested.literals();
  static inline const uint64_t test_doubled =
      test_nested.lit_map([](uint64_t n) { return (n * UINT64_C(2)); }).eval();
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<
                  std::pair<
                      std::pair<
                          std::pair<
                              std::pair<std::pair<std::pair<std::pair<uint64_t,
                                                                      uint64_t>,
                                                            uint64_t>,
                                                  uint64_t>,
                                        uint64_t>,
                              uint64_t>,
                          uint64_t>,
                      uint64_t>,
                  uint64_t>,
              uint64_t>,
          List<uint64_t>>,
      uint64_t>
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
