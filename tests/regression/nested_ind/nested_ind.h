#ifndef INCLUDED_NESTED_IND
#define INCLUDED_NESTED_IND

#include <algorithm>
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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return List<t_A>::cons(d_a0, d_a1->app(m));
    }
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

  public:
    // CREATORS
    explicit custom_list(Cnil _v) : d_v_(_v) {}

    explicit custom_list(Ccons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<custom_list<t_A>> cnil() {
      return std::make_shared<custom_list<t_A>>(Cnil{});
    }

    static std::shared_ptr<custom_list<t_A>>
    ccons(t_A a0, const std::shared_ptr<custom_list<t_A>> &a1) {
      return std::make_shared<custom_list<t_A>>(Ccons{std::move(a0), a1});
    }

    static std::shared_ptr<custom_list<t_A>>
    ccons(t_A a0, std::shared_ptr<custom_list<t_A>> &&a1) {
      return std::make_shared<custom_list<t_A>>(
          Ccons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int custom_list_length() const {
      if (std::holds_alternative<typename custom_list<t_A>::Cnil>(this->v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename custom_list<t_A>::Ccons>(this->v());
        return (1u + d_a1->custom_list_length());
      }
    }

    template <typename T1,
              MapsTo<T1, t_A, std::shared_ptr<custom_list<t_A>>, T1> F1>
    T1 custom_list_rec(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename custom_list<t_A>::Cnil>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename custom_list<t_A>::Ccons>(this->v());
        return f0(d_a0, d_a1, d_a1->template custom_list_rec<T1>(f, f0));
      }
    }

    template <typename T1,
              MapsTo<T1, t_A, std::shared_ptr<custom_list<t_A>>, T1> F1>
    T1 custom_list_rect(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename custom_list<t_A>::Cnil>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename custom_list<t_A>::Ccons>(this->v());
        return f0(d_a0, d_a1, d_a1->template custom_list_rect<T1>(f, f0));
      }
    }
  };

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

  public:
    // CREATORS
    explicit rose(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<rose<t_A>>
    node(t_A a0,
         const std::shared_ptr<custom_list<std::shared_ptr<rose<t_A>>>> &a1) {
      return std::make_shared<rose<t_A>>(Node{std::move(a0), a1});
    }

    static std::shared_ptr<rose<t_A>>
    node(t_A a0,
         std::shared_ptr<custom_list<std::shared_ptr<rose<t_A>>>> &&a1) {
      return std::make_shared<rose<t_A>>(Node{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int children_count() const {
      const auto &[d_a0, d_a1] = std::get<typename rose<t_A>::Node>(this->v());
      return d_a1->custom_list_length();
    }

    t_A root() const {
      const auto &[d_a0, d_a1] = std::get<typename rose<t_A>::Node>(this->v());
      return d_a0;
    }

    template <typename T1,
              MapsTo<T1, t_A,
                     std::shared_ptr<custom_list<std::shared_ptr<rose<t_A>>>>>
                  F0>
    T1 rose_rec(F0 &&f) const {
      const auto &[d_a0, d_a1] = std::get<typename rose<t_A>::Node>(this->v());
      return f(d_a0, d_a1);
    }

    template <typename T1,
              MapsTo<T1, t_A,
                     std::shared_ptr<custom_list<std::shared_ptr<rose<t_A>>>>>
                  F0>
    T1 rose_rect(F0 &&f) const {
      const auto &[d_a0, d_a1] = std::get<typename rose<t_A>::Node>(this->v());
      return f(d_a0, d_a1);
    }
  };

  static std::shared_ptr<rose<unsigned int>> leaf(const unsigned int n);
  static inline const std::shared_ptr<rose<unsigned int>> small_tree =
      rose<unsigned int>::node(
          1u,
          custom_list<std::shared_ptr<rose<unsigned int>>>::ccons(
              leaf(2u),
              custom_list<std::shared_ptr<rose<unsigned int>>>::ccons(
                  leaf(3u),
                  custom_list<std::shared_ptr<rose<unsigned int>>>::cnil())));
  static inline const std::shared_ptr<rose<unsigned int>> bigger_tree =
      rose<unsigned int>::node(
          1u,
          custom_list<std::shared_ptr<rose<unsigned int>>>::ccons(
              small_tree,
              custom_list<std::shared_ptr<rose<unsigned int>>>::ccons(
                  leaf(4u),
                  custom_list<std::shared_ptr<rose<unsigned int>>>::cnil())));
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

  public:
    // CREATORS
    explicit expr(Lit _v) : d_v_(std::move(_v)) {}

    explicit expr(Add _v) : d_v_(std::move(_v)) {}

    explicit expr(Mul _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<expr> lit(unsigned int a0) {
      return std::make_shared<expr>(Lit{std::move(a0)});
    }

    static std::shared_ptr<expr>
    add(const std::shared_ptr<List<std::shared_ptr<expr>>> &a0) {
      return std::make_shared<expr>(Add{a0});
    }

    static std::shared_ptr<expr>
    add(std::shared_ptr<List<std::shared_ptr<expr>>> &&a0) {
      return std::make_shared<expr>(Add{std::move(a0)});
    }

    static std::shared_ptr<expr>
    mul(const std::shared_ptr<List<std::shared_ptr<expr>>> &a0) {
      return std::make_shared<expr>(Mul{a0});
    }

    static std::shared_ptr<expr>
    mul(std::shared_ptr<List<std::shared_ptr<expr>>> &&a0) {
      return std::make_shared<expr>(Mul{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <MapsTo<unsigned int, unsigned int> F0>
    std::shared_ptr<expr> lit_map(F0 &&f) const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[d_a0] = std::get<typename expr::Lit>(this->v());
        return expr::lit(f(d_a0));
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(this->v());
        return expr::add([&]() {
          std::function<std::shared_ptr<List<std::shared_ptr<expr>>>(
              std::shared_ptr<List<std::shared_ptr<expr>>>)>
              aux;
          aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
              -> std::shared_ptr<List<std::shared_ptr<expr>>> {
            if (std::holds_alternative<
                    typename List<std::shared_ptr<expr>>::Nil>(l->v())) {
              return List<std::shared_ptr<expr>>::nil();
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<std::shared_ptr<expr>>::Cons>(l->v());
              return List<std::shared_ptr<expr>>::cons(d_a0->lit_map(f),
                                                       aux(d_a1));
            }
          };
          return aux(d_a0);
        }());
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(this->v());
        return expr::mul([&]() {
          std::function<std::shared_ptr<List<std::shared_ptr<expr>>>(
              std::shared_ptr<List<std::shared_ptr<expr>>>)>
              aux;
          aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
              -> std::shared_ptr<List<std::shared_ptr<expr>>> {
            if (std::holds_alternative<
                    typename List<std::shared_ptr<expr>>::Nil>(l->v())) {
              return List<std::shared_ptr<expr>>::nil();
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<std::shared_ptr<expr>>::Cons>(l->v());
              return List<std::shared_ptr<expr>>::cons(d_a0->lit_map(f),
                                                       aux(d_a1));
            }
          };
          return aux(d_a0);
        }());
      }
    }

    std::shared_ptr<List<unsigned int>> literals() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[d_a0] = std::get<typename expr::Lit>(this->v());
        return List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(this->v());
        std::function<std::shared_ptr<List<unsigned int>>(
            std::shared_ptr<List<std::shared_ptr<expr>>>)>
            aux;
        aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
            -> std::shared_ptr<List<unsigned int>> {
          if (std::holds_alternative<typename List<std::shared_ptr<expr>>::Nil>(
                  l->v())) {
            return List<unsigned int>::nil();
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<std::shared_ptr<expr>>::Cons>(l->v());
            return d_a00->literals()->app(aux(d_a10));
          }
        };
        return aux(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(this->v());
        std::function<std::shared_ptr<List<unsigned int>>(
            std::shared_ptr<List<std::shared_ptr<expr>>>)>
            aux;
        aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
            -> std::shared_ptr<List<unsigned int>> {
          if (std::holds_alternative<typename List<std::shared_ptr<expr>>::Nil>(
                  l->v())) {
            return List<unsigned int>::nil();
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<std::shared_ptr<expr>>::Cons>(l->v());
            return d_a00->literals()->app(aux(d_a10));
          }
        };
        return aux(d_a0);
      }
    }

    __attribute__((pure)) unsigned int expr_depth() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        return 0u;
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(this->v());
        return ([&]() {
          std::function<unsigned int(
              std::shared_ptr<List<std::shared_ptr<expr>>>)>
              aux;
          aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
              -> unsigned int {
            if (std::holds_alternative<
                    typename List<std::shared_ptr<expr>>::Nil>(l->v())) {
              return 0u;
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<std::shared_ptr<expr>>::Cons>(l->v());
              return std::max(d_a0->expr_depth(), aux(d_a1));
            }
          };
          return aux(d_a0);
        }() + 1);
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(this->v());
        return ([&]() {
          std::function<unsigned int(
              std::shared_ptr<List<std::shared_ptr<expr>>>)>
              aux;
          aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
              -> unsigned int {
            if (std::holds_alternative<
                    typename List<std::shared_ptr<expr>>::Nil>(l->v())) {
              return 0u;
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<std::shared_ptr<expr>>::Cons>(l->v());
              return std::max(d_a0->expr_depth(), aux(d_a1));
            }
          };
          return aux(d_a0);
        }() + 1);
      }
    }

    __attribute__((pure)) unsigned int expr_size() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        return 1u;
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(this->v());
        return ([&]() {
          std::function<unsigned int(
              std::shared_ptr<List<std::shared_ptr<expr>>>)>
              aux;
          aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
              -> unsigned int {
            if (std::holds_alternative<
                    typename List<std::shared_ptr<expr>>::Nil>(l->v())) {
              return 0u;
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<std::shared_ptr<expr>>::Cons>(l->v());
              return (d_a0->expr_size() + aux(d_a1));
            }
          };
          return aux(d_a0);
        }() + 1);
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(this->v());
        return ([&]() {
          std::function<unsigned int(
              std::shared_ptr<List<std::shared_ptr<expr>>>)>
              aux;
          aux = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
              -> unsigned int {
            if (std::holds_alternative<
                    typename List<std::shared_ptr<expr>>::Nil>(l->v())) {
              return 0u;
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<std::shared_ptr<expr>>::Cons>(l->v());
              return (d_a0->expr_size() + aux(d_a1));
            }
          };
          return aux(d_a0);
        }() + 1);
      }
    }

    __attribute__((pure)) unsigned int eval() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[d_a0] = std::get<typename expr::Lit>(this->v());
        return d_a0;
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(this->v());
        std::function<unsigned int(
            std::shared_ptr<List<std::shared_ptr<expr>>>)>
            sum_all;
        sum_all = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
            -> unsigned int {
          if (std::holds_alternative<typename List<std::shared_ptr<expr>>::Nil>(
                  l->v())) {
            return 0u;
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<std::shared_ptr<expr>>::Cons>(l->v());
            return (d_a00->eval() + sum_all(d_a10));
          }
        };
        return sum_all(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(this->v());
        std::function<unsigned int(
            std::shared_ptr<List<std::shared_ptr<expr>>>)>
            prod_all;
        prod_all = [&](std::shared_ptr<List<std::shared_ptr<expr>>> l)
            -> unsigned int {
          if (std::holds_alternative<typename List<std::shared_ptr<expr>>::Nil>(
                  l->v())) {
            return 1u;
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<std::shared_ptr<expr>>::Cons>(l->v());
            return (d_a00->eval() * prod_all(d_a10));
          }
        };
        return prod_all(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<List<std::shared_ptr<expr>>>> F1,
              MapsTo<T1, std::shared_ptr<List<std::shared_ptr<expr>>>> F2>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[d_a0] = std::get<typename expr::Lit>(this->v());
        return f(d_a0);
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(this->v());
        return f0(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(this->v());
        return f1(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<List<std::shared_ptr<expr>>>> F1,
              MapsTo<T1, std::shared_ptr<List<std::shared_ptr<expr>>>> F2>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[d_a0] = std::get<typename expr::Lit>(this->v());
        return f(d_a0);
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(this->v());
        return f0(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(this->v());
        return f1(d_a0);
      }
    }
  };

  static inline const std::shared_ptr<expr> test_add =
      expr::add(List<std::shared_ptr<expr>>::cons(
          expr::lit(1u),
          List<std::shared_ptr<expr>>::cons(
              expr::lit(2u),
              List<std::shared_ptr<expr>>::cons(
                  expr::lit(3u), List<std::shared_ptr<expr>>::nil()))));
  static inline const std::shared_ptr<expr> test_mul =
      expr::mul(List<std::shared_ptr<expr>>::cons(
          expr::lit(2u),
          List<std::shared_ptr<expr>>::cons(
              expr::lit(3u),
              List<std::shared_ptr<expr>>::cons(
                  expr::lit(4u), List<std::shared_ptr<expr>>::nil()))));
  static inline const std::shared_ptr<expr> test_nested =
      expr::mul(List<std::shared_ptr<expr>>::cons(
          expr::add(List<std::shared_ptr<expr>>::cons(
              expr::lit(1u),
              List<std::shared_ptr<expr>>::cons(
                  expr::lit(2u), List<std::shared_ptr<expr>>::nil()))),
          List<std::shared_ptr<expr>>::cons(
              expr::add(List<std::shared_ptr<expr>>::cons(
                  expr::lit(3u),
                  List<std::shared_ptr<expr>>::cons(
                      expr::lit(4u), List<std::shared_ptr<expr>>::nil()))),
              List<std::shared_ptr<expr>>::nil())));
  static inline const unsigned int test_eval_add = test_add->eval();
  static inline const unsigned int test_eval_mul = test_mul->eval();
  static inline const unsigned int test_eval_nested = test_nested->eval();
  static inline const unsigned int test_size_nested = test_nested->expr_size();
  static inline const unsigned int test_depth_nested =
      test_nested->expr_depth();
  static inline const std::shared_ptr<List<unsigned int>> test_literals =
      test_nested->literals();
  static inline const unsigned int test_doubled =
      test_nested->lit_map([](const unsigned int n) { return (n * 2u); })
          ->eval();
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
