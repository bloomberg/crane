#ifndef INCLUDED_FUNCTION_VERNAC
#define INCLUDED_FUNCTION_VERNAC

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
};

template <typename t_A> struct Sig {
  // TYPES
  struct Exist {
    t_A d_x;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Sig<t_A>> exist(t_A x) {
    return std::make_shared<Sig<t_A>>(Exist{std::move(x)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct FunctionVernac {
  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int div2_F(F0 &&div3,
                                                   const unsigned int n) {
    if (n <= 0) {
      return 0u;
    } else {
      unsigned int n0 = n - 1;
      if (n0 <= 0) {
        return 0u;
      } else {
        unsigned int p = n0 - 1;
        return (div3(p) + 1);
      }
    }
  }

  static std::shared_ptr<Sig<unsigned int>>
  div2_terminate(const unsigned int n);
  __attribute__((pure)) static unsigned int div2(const unsigned int n);

  struct R_div2 {
    // TYPES
    struct R_div2_0 {
      unsigned int d_n;
    };

    struct R_div2_1 {
      unsigned int d_n;
    };

    struct R_div2_2 {
      unsigned int d_n;
      unsigned int d_p;
      unsigned int d_a2;
      std::shared_ptr<R_div2> d__res;
    };

    using variant_t = std::variant<R_div2_0, R_div2_1, R_div2_2>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit R_div2(R_div2_0 _v) : d_v_(std::move(_v)) {}

    explicit R_div2(R_div2_1 _v) : d_v_(std::move(_v)) {}

    explicit R_div2(R_div2_2 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<R_div2> r_div2_0(unsigned int n) {
      return std::make_shared<R_div2>(R_div2_0{std::move(n)});
    }

    static std::shared_ptr<R_div2> r_div2_1(unsigned int n) {
      return std::make_shared<R_div2>(R_div2_1{std::move(n)});
    }

    static std::shared_ptr<R_div2>
    r_div2_2(unsigned int n, unsigned int p, unsigned int a2,
             const std::shared_ptr<R_div2> &_res) {
      return std::make_shared<R_div2>(
          R_div2_2{std::move(n), std::move(p), std::move(a2), _res});
    }

    static std::shared_ptr<R_div2> r_div2_2(unsigned int n, unsigned int p,
                                            unsigned int a2,
                                            std::shared_ptr<R_div2> &&_res) {
      return std::make_shared<R_div2>(
          R_div2_2{std::move(n), std::move(p), std::move(a2), std::move(_res)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1,
              MapsTo<T1, unsigned int, unsigned int, unsigned int,
                     std::shared_ptr<R_div2>, T1>
                  F2>
    T1 R_div2_rec(F0 &&f, F1 &&f0, F2 &&f1, const unsigned int,
                  const unsigned int) const {
      return std::visit(
          Overloaded{[&](const typename R_div2::R_div2_0 &_args) -> T1 {
                       return f(_args.d_n);
                     },
                     [&](const typename R_div2::R_div2_1 &_args) -> T1 {
                       return f0(_args.d_n);
                     },
                     [&](const typename R_div2::R_div2_2 &_args) -> T1 {
                       return f1(_args.d_n, _args.d_p, _args.d_a2, _args.d__res,
                                 _args.d__res->template R_div2_rec<T1>(
                                     f, f0, f1, _args.d_p, _args.d_a2));
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1,
              MapsTo<T1, unsigned int, unsigned int, unsigned int,
                     std::shared_ptr<R_div2>, T1>
                  F2>
    T1 R_div2_rect(F0 &&f, F1 &&f0, F2 &&f1, const unsigned int,
                   const unsigned int) const {
      return std::visit(
          Overloaded{[&](const typename R_div2::R_div2_0 &_args) -> T1 {
                       return f(_args.d_n);
                     },
                     [&](const typename R_div2::R_div2_1 &_args) -> T1 {
                       return f0(_args.d_n);
                     },
                     [&](const typename R_div2::R_div2_2 &_args) -> T1 {
                       return f1(_args.d_n, _args.d_p, _args.d_a2, _args.d__res,
                                 _args.d__res->template R_div2_rect<T1>(
                                     f, f0, f1, _args.d_p, _args.d_a2));
                     }},
          this->v());
    }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int, unsigned int, T1> F2>
  static T1 div2_rect(F0 &&f, F1 &&f0, F2 &&f1, const unsigned int n) {
    std::function<T1(unsigned int, T1)> f2 =
        [=](unsigned int _pa0, T1 _pa1) mutable { return f1(n, _pa0, _pa1); };
    T1 f3 = f0(n);
    T1 f4 = f(n);
    if (n <= 0) {
      return f4;
    } else {
      unsigned int n0 = n - 1;
      if (n0 <= 0) {
        return f3;
      } else {
        unsigned int n1 = n0 - 1;
        std::function<T1(T1)> f5 = [=](T1 _pa0) mutable {
          return f2(n1, _pa0);
        };
        T1 hrec = div2_rect<T1>(f, f0, f1, n1);
        return f5(hrec);
      }
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int, unsigned int, T1> F2>
  static T1 div2_rec(F0 &&_x0, F1 &&_x1, F2 &&_x2, const unsigned int _x3) {
    return div2_rect<T1>(_x0, _x1, _x2, _x3);
  }

  static std::shared_ptr<R_div2> R_div2_correct(const unsigned int n,
                                                const unsigned int _res);

  template <MapsTo<unsigned int, std::shared_ptr<List<unsigned int>>> F0>
  __attribute__((pure)) static unsigned int
  list_sum_F(F0 &&list_sum0, const std::shared_ptr<List<unsigned int>> &l) {
    return std::visit(
        Overloaded{[](const typename List<unsigned int>::Nil &)
                       -> unsigned int { return 0u; },
                   [&](const typename List<unsigned int>::Cons &_args)
                       -> unsigned int {
                     return (_args.d_a0 + list_sum0(_args.d_a1));
                   }},
        l->v());
  }

  static std::shared_ptr<Sig<unsigned int>>
  list_sum_terminate(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  list_sum(const std::shared_ptr<List<unsigned int>> &l);

  struct R_list_sum {
    // TYPES
    struct R_list_sum_0 {
      std::shared_ptr<List<unsigned int>> d_l;
    };

    struct R_list_sum_1 {
      std::shared_ptr<List<unsigned int>> d_l;
      unsigned int d_x;
      std::shared_ptr<List<unsigned int>> d_xs;
      unsigned int d_a3;
      std::shared_ptr<R_list_sum> d__res;
    };

    using variant_t = std::variant<R_list_sum_0, R_list_sum_1>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit R_list_sum(R_list_sum_0 _v) : d_v_(std::move(_v)) {}

    explicit R_list_sum(R_list_sum_1 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<R_list_sum>
    r_list_sum_0(const std::shared_ptr<List<unsigned int>> &l) {
      return std::make_shared<R_list_sum>(R_list_sum_0{l});
    }

    static std::shared_ptr<R_list_sum>
    r_list_sum_0(std::shared_ptr<List<unsigned int>> &&l) {
      return std::make_shared<R_list_sum>(R_list_sum_0{std::move(l)});
    }

    static std::shared_ptr<R_list_sum>
    r_list_sum_1(const std::shared_ptr<List<unsigned int>> &l, unsigned int x,
                 const std::shared_ptr<List<unsigned int>> &xs, unsigned int a3,
                 const std::shared_ptr<R_list_sum> &_res) {
      return std::make_shared<R_list_sum>(
          R_list_sum_1{l, std::move(x), xs, std::move(a3), _res});
    }

    static std::shared_ptr<R_list_sum>
    r_list_sum_1(std::shared_ptr<List<unsigned int>> &&l, unsigned int x,
                 std::shared_ptr<List<unsigned int>> &&xs, unsigned int a3,
                 std::shared_ptr<R_list_sum> &&_res) {
      return std::make_shared<R_list_sum>(
          R_list_sum_1{std::move(l), std::move(x), std::move(xs), std::move(a3),
                       std::move(_res)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, std::shared_ptr<List<unsigned int>>> F0,
              MapsTo<T1, std::shared_ptr<List<unsigned int>>, unsigned int,
                     std::shared_ptr<List<unsigned int>>, unsigned int,
                     std::shared_ptr<R_list_sum>, T1>
                  F1>
    T1 R_list_sum_rec(F0 &&f, F1 &&f0,
                      const std::shared_ptr<List<unsigned int>> &,
                      const unsigned int) const {
      return std::visit(
          Overloaded{[&](const typename R_list_sum::R_list_sum_0 &_args) -> T1 {
                       return f(_args.d_l);
                     },
                     [&](const typename R_list_sum::R_list_sum_1 &_args) -> T1 {
                       return f0(_args.d_l, _args.d_x, _args.d_xs, _args.d_a3,
                                 _args.d__res,
                                 _args.d__res->template R_list_sum_rec<T1>(
                                     f, f0, _args.d_xs, _args.d_a3));
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<List<unsigned int>>> F0,
              MapsTo<T1, std::shared_ptr<List<unsigned int>>, unsigned int,
                     std::shared_ptr<List<unsigned int>>, unsigned int,
                     std::shared_ptr<R_list_sum>, T1>
                  F1>
    T1 R_list_sum_rect(F0 &&f, F1 &&f0,
                       const std::shared_ptr<List<unsigned int>> &,
                       const unsigned int) const {
      return std::visit(
          Overloaded{[&](const typename R_list_sum::R_list_sum_0 &_args) -> T1 {
                       return f(_args.d_l);
                     },
                     [&](const typename R_list_sum::R_list_sum_1 &_args) -> T1 {
                       return f0(_args.d_l, _args.d_x, _args.d_xs, _args.d_a3,
                                 _args.d__res,
                                 _args.d__res->template R_list_sum_rect<T1>(
                                     f, f0, _args.d_xs, _args.d_a3));
                     }},
          this->v());
    }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<List<unsigned int>>> F0,
            MapsTo<T1, std::shared_ptr<List<unsigned int>>, unsigned int,
                   std::shared_ptr<List<unsigned int>>, T1>
                F1>
  static T1 list_sum_rect(F0 &&f, F1 &&f0,
                          const std::shared_ptr<List<unsigned int>> &l) {
    std::function<T1(unsigned int, std::shared_ptr<List<unsigned int>>, T1)>
        f1 = [=](unsigned int _pa0, std::shared_ptr<List<unsigned int>> _pa1,
                 T1 _pa2) mutable { return f0(l, _pa0, _pa1, _pa2); };
    T1 f2 = f(l);
    return std::visit(
        Overloaded{[&](const typename List<unsigned int>::Nil &) -> auto {
                     return f2;
                   },
                   [&](const typename List<unsigned int>::Cons &_args) -> auto {
                     std::function<T1(T1)> f3 = [=](T1 _pa0) mutable {
                       return f1(_args.d_a0, _args.d_a1, _pa0);
                     };
                     T1 hrec = list_sum_rect<T1>(f, f0, _args.d_a1);
                     return f3(hrec);
                   }},
        l->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<List<unsigned int>>> F0,
            MapsTo<T1, std::shared_ptr<List<unsigned int>>, unsigned int,
                   std::shared_ptr<List<unsigned int>>, T1>
                F1>
  static T1 list_sum_rec(F0 &&_x0, F1 &&_x1,
                         const std::shared_ptr<List<unsigned int>> &_x2) {
    return list_sum_rect<T1>(_x0, _x1, _x2);
  }

  static std::shared_ptr<R_list_sum>
  R_list_sum_correct(const std::shared_ptr<List<unsigned int>> &l,
                     const unsigned int _res);
  static inline const unsigned int test_div2 = div2(10u);
  static inline const unsigned int test_sum = list_sum(List<unsigned int>::cons(
      1u, List<unsigned int>::cons(
              2u, List<unsigned int>::cons(
                      3u, List<unsigned int>::cons(
                              4u, List<unsigned int>::cons(
                                      5u, List<unsigned int>::nil()))))));
};

#endif // INCLUDED_FUNCTION_VERNAC
