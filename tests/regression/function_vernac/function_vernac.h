#ifndef INCLUDED_FUNCTION_VERNAC
#define INCLUDED_FUNCTION_VERNAC

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
};

template <typename t_A> struct Sig {
  // TYPES
  struct Exist {
    t_A d_a0;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Sig<t_A>> Exist_(t_A a0) {
      return std::shared_ptr<Sig<t_A>>(new Sig<t_A>(Exist{a0}));
    }

    static std::unique_ptr<Sig<t_A>> Exist_uptr(t_A a0) {
      return std::unique_ptr<Sig<t_A>>(new Sig<t_A>(Exist{a0}));
    }
  };

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
      unsigned int d_a0;
    };

    struct R_div2_1 {
      unsigned int d_a0;
    };

    struct R_div2_2 {
      unsigned int d_a0;
      unsigned int d_a1;
      unsigned int d_a2;
      std::shared_ptr<R_div2> d_a3;
    };

    using variant_t = std::variant<R_div2_0, R_div2_1, R_div2_2>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit R_div2(R_div2_0 _v) : d_v_(std::move(_v)) {}

    explicit R_div2(R_div2_1 _v) : d_v_(std::move(_v)) {}

    explicit R_div2(R_div2_2 _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<R_div2> R_div2_0_(unsigned int a0) {
        return std::shared_ptr<R_div2>(new R_div2(R_div2_0{a0}));
      }

      static std::shared_ptr<R_div2> R_div2_1_(unsigned int a0) {
        return std::shared_ptr<R_div2>(new R_div2(R_div2_1{a0}));
      }

      static std::shared_ptr<R_div2>
      R_div2_2_(unsigned int a0, unsigned int a1, unsigned int a2,
                const std::shared_ptr<R_div2> &a3) {
        return std::shared_ptr<R_div2>(new R_div2(R_div2_2{a0, a1, a2, a3}));
      }

      static std::unique_ptr<R_div2> R_div2_0_uptr(unsigned int a0) {
        return std::unique_ptr<R_div2>(new R_div2(R_div2_0{a0}));
      }

      static std::unique_ptr<R_div2> R_div2_1_uptr(unsigned int a0) {
        return std::unique_ptr<R_div2>(new R_div2(R_div2_1{a0}));
      }

      static std::unique_ptr<R_div2>
      R_div2_2_uptr(unsigned int a0, unsigned int a1, unsigned int a2,
                    const std::shared_ptr<R_div2> &a3) {
        return std::unique_ptr<R_div2>(new R_div2(R_div2_2{a0, a1, a2, a3}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int, unsigned int, unsigned int,
                   std::shared_ptr<R_div2>, T1>
                F2>
  static T1 R_div2_rect(F0 &&f, F1 &&f0, F2 &&f1, const unsigned int _x,
                        const unsigned int _x0,
                        const std::shared_ptr<R_div2> &r) {
    return std::visit(
        Overloaded{[&](const typename R_div2::R_div2_0 _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f(std::move(n));
                   },
                   [&](const typename R_div2::R_div2_1 _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f0(std::move(n));
                   },
                   [&](const typename R_div2::R_div2_2 _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     unsigned int p = _args.d_a1;
                     unsigned int _res = _args.d_a2;
                     std::shared_ptr<R_div2> r0 = _args.d_a3;
                     return f1(std::move(n), p, _res, r0,
                               R_div2_rect<T1>(f, f0, f1, p, _res, r0));
                   }},
        r->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int, unsigned int, unsigned int,
                   std::shared_ptr<R_div2>, T1>
                F2>
  static T1 R_div2_rec(F0 &&f, F1 &&f0, F2 &&f1, const unsigned int _x,
                       const unsigned int _x0,
                       const std::shared_ptr<R_div2> &r) {
    return std::visit(
        Overloaded{[&](const typename R_div2::R_div2_0 _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f(std::move(n));
                   },
                   [&](const typename R_div2::R_div2_1 _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f0(std::move(n));
                   },
                   [&](const typename R_div2::R_div2_2 _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     unsigned int p = _args.d_a1;
                     unsigned int _res = _args.d_a2;
                     std::shared_ptr<R_div2> r0 = _args.d_a3;
                     return f1(std::move(n), p, _res, r0,
                               R_div2_rec<T1>(f, f0, f1, p, _res, r0));
                   }},
        r->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int, unsigned int, T1> F2>
  static T1 div2_rect(F0 &&f, F1 &&f0, F2 &&f1, const unsigned int n) {
    std::function<T1(unsigned int, T1)> f2 = f1(n);
    T1 f3 = f0(n);
    T1 f4 = f(n);
    if (n <= 0) {
      return f4();
    } else {
      unsigned int n0 = n - 1;
      if (n0 <= 0) {
        return f3();
      } else {
        unsigned int n1 = n0 - 1;
        std::function<T1(T1)> f5 = f2(n1);
        T1 hrec = div2_rect<T1>(f, f0, f1, n1);
        return f5(hrec);
      }
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int, unsigned int, T1> F2>
  static T1 div2_rec(F0 &&_x0, F1 &&_x1, F2 &&_x2, const unsigned int _x3) {
    return div2_rect(_x0, _x1, _x2, _x3);
  }

  static std::shared_ptr<R_div2> R_div2_correct(const unsigned int n,
                                                const unsigned int _res);

  template <MapsTo<unsigned int, std::shared_ptr<List<unsigned int>>> F0>
  __attribute__((pure)) static unsigned int
  list_sum_F(F0 &&list_sum0, const std::shared_ptr<List<unsigned int>> &l) {
    return std::visit(
        Overloaded{
            [](const typename List<unsigned int>::Nil _args) -> unsigned int {
              return 0u;
            },
            [&](const typename List<unsigned int>::Cons _args) -> unsigned int {
              unsigned int x = _args.d_a0;
              std::shared_ptr<List<unsigned int>> xs = _args.d_a1;
              return (std::move(x) + list_sum0(std::move(xs)));
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
      std::shared_ptr<List<unsigned int>> d_a0;
    };

    struct R_list_sum_1 {
      std::shared_ptr<List<unsigned int>> d_a0;
      unsigned int d_a1;
      std::shared_ptr<List<unsigned int>> d_a2;
      unsigned int d_a3;
      std::shared_ptr<R_list_sum> d_a4;
    };

    using variant_t = std::variant<R_list_sum_0, R_list_sum_1>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit R_list_sum(R_list_sum_0 _v) : d_v_(std::move(_v)) {}

    explicit R_list_sum(R_list_sum_1 _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<R_list_sum>
      R_list_sum_0_(const std::shared_ptr<List<unsigned int>> &a0) {
        return std::shared_ptr<R_list_sum>(new R_list_sum(R_list_sum_0{a0}));
      }

      static std::shared_ptr<R_list_sum>
      R_list_sum_1_(const std::shared_ptr<List<unsigned int>> &a0,
                    unsigned int a1,
                    const std::shared_ptr<List<unsigned int>> &a2,
                    unsigned int a3, const std::shared_ptr<R_list_sum> &a4) {
        return std::shared_ptr<R_list_sum>(
            new R_list_sum(R_list_sum_1{a0, a1, a2, a3, a4}));
      }

      static std::unique_ptr<R_list_sum>
      R_list_sum_0_uptr(const std::shared_ptr<List<unsigned int>> &a0) {
        return std::unique_ptr<R_list_sum>(new R_list_sum(R_list_sum_0{a0}));
      }

      static std::unique_ptr<R_list_sum> R_list_sum_1_uptr(
          const std::shared_ptr<List<unsigned int>> &a0, unsigned int a1,
          const std::shared_ptr<List<unsigned int>> &a2, unsigned int a3,
          const std::shared_ptr<R_list_sum> &a4) {
        return std::unique_ptr<R_list_sum>(
            new R_list_sum(R_list_sum_1{a0, a1, a2, a3, a4}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<List<unsigned int>>> F0,
            MapsTo<T1, std::shared_ptr<List<unsigned int>>, unsigned int,
                   std::shared_ptr<List<unsigned int>>, unsigned int,
                   std::shared_ptr<R_list_sum>, T1>
                F1>
  static T1 R_list_sum_rect(F0 &&f, F1 &&f0,
                            const std::shared_ptr<List<unsigned int>> &_x,
                            const unsigned int _x0,
                            const std::shared_ptr<R_list_sum> &r) {
    return std::visit(
        Overloaded{[&](const typename R_list_sum::R_list_sum_0 _args) -> T1 {
                     std::shared_ptr<List<unsigned int>> l = _args.d_a0;
                     return f(std::move(l));
                   },
                   [&](const typename R_list_sum::R_list_sum_1 _args) -> T1 {
                     std::shared_ptr<List<unsigned int>> l = _args.d_a0;
                     unsigned int x = _args.d_a1;
                     std::shared_ptr<List<unsigned int>> xs = _args.d_a2;
                     unsigned int _res = _args.d_a3;
                     std::shared_ptr<R_list_sum> r0 = _args.d_a4;
                     return f0(std::move(l), std::move(x), xs, _res, r0,
                               R_list_sum_rect<T1>(f, f0, xs, _res, r0));
                   }},
        r->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<List<unsigned int>>> F0,
            MapsTo<T1, std::shared_ptr<List<unsigned int>>, unsigned int,
                   std::shared_ptr<List<unsigned int>>, unsigned int,
                   std::shared_ptr<R_list_sum>, T1>
                F1>
  static T1
  R_list_sum_rec(F0 &&f, F1 &&f0, const std::shared_ptr<List<unsigned int>> &_x,
                 const unsigned int _x0, const std::shared_ptr<R_list_sum> &r) {
    return std::visit(
        Overloaded{[&](const typename R_list_sum::R_list_sum_0 _args) -> T1 {
                     std::shared_ptr<List<unsigned int>> l = _args.d_a0;
                     return f(std::move(l));
                   },
                   [&](const typename R_list_sum::R_list_sum_1 _args) -> T1 {
                     std::shared_ptr<List<unsigned int>> l = _args.d_a0;
                     unsigned int x = _args.d_a1;
                     std::shared_ptr<List<unsigned int>> xs = _args.d_a2;
                     unsigned int _res = _args.d_a3;
                     std::shared_ptr<R_list_sum> r0 = _args.d_a4;
                     return f0(std::move(l), std::move(x), xs, _res, r0,
                               R_list_sum_rec<T1>(f, f0, xs, _res, r0));
                   }},
        r->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<List<unsigned int>>> F0,
            MapsTo<T1, std::shared_ptr<List<unsigned int>>, unsigned int,
                   std::shared_ptr<List<unsigned int>>, T1>
                F1>
  static T1 list_sum_rect(F0 &&f, F1 &&f0,
                          const std::shared_ptr<List<unsigned int>> &l) {
    std::function<T1(unsigned int, std::shared_ptr<List<unsigned int>>, T1)>
        f1 = f0(l);
    T1 f2 = f(l);
    return std::visit(
        Overloaded{[&](const typename List<unsigned int>::Nil _args) -> auto {
                     return f2();
                   },
                   [&](const typename List<unsigned int>::Cons _args) -> auto {
                     unsigned int n = _args.d_a0;
                     std::shared_ptr<List<unsigned int>> l0 = _args.d_a1;
                     std::function<T1(T1)> f3 = f1(std::move(n), std::move(l0));
                     T1 hrec = list_sum_rect<T1>(f, f0, std::move(l0));
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
    return list_sum_rect(_x0, _x1, _x2);
  }

  static std::shared_ptr<R_list_sum>
  R_list_sum_correct(const std::shared_ptr<List<unsigned int>> &l,
                     const unsigned int _res);
  static inline const unsigned int test_div2 = div2(10u);
  static inline const unsigned int test_sum =
      list_sum(List<unsigned int>::ctor::Cons_(
          1u,
          List<unsigned int>::ctor::Cons_(
              2u,
              List<unsigned int>::ctor::Cons_(
                  3u, List<unsigned int>::ctor::Cons_(
                          4u, List<unsigned int>::ctor::Cons_(
                                  5u, List<unsigned int>::ctor::Nil_()))))));
};

#endif // INCLUDED_FUNCTION_VERNAC
