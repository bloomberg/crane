#ifndef INCLUDED_EQUATIONS
#define INCLUDED_EQUATIONS

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

struct PeanoNat {
  __attribute__((pure)) static bool leb(const unsigned int n,
                                        const unsigned int m);
  __attribute__((pure)) static bool ltb(const unsigned int n,
                                        const unsigned int m);
  __attribute__((pure)) static bool even(const unsigned int n);
  __attribute__((pure)) static unsigned int div2(const unsigned int n);
};

template <typename I, typename t_A>
concept FunctionalInduction =
    requires { typename I::fun_ind_prf_ty; } && requires {
      { I::fun_ind_prf() } -> std::convertible_to<typename I::fun_ind_prf_ty>;
    } || requires {
      { I::fun_ind_prf } -> std::convertible_to<typename I::fun_ind_prf_ty>;
    };

struct Equations {
  template <MapsTo<unsigned int, std::pair<unsigned int, unsigned int>> F3>
  __attribute__((pure)) static unsigned int
  gcd_clause_3(const unsigned int n, const unsigned int n0, const bool refine,
               F3 &&gcd0) {
    if (refine) {
      return gcd0(std::make_pair(
          (n + 1), ((((std::move(n0) + 1) - (n + 1)) > (std::move(n0) + 1)
                         ? 0
                         : ((std::move(n0) + 1) - (n + 1))))));
    } else {
      return gcd0(
          std::make_pair(((((std::move(n) + 1) - (n0 + 1)) > (std::move(n) + 1)
                               ? 0
                               : ((std::move(n) + 1) - (n0 + 1)))),
                         (n0 + 1)));
    }
  }

  template <MapsTo<unsigned int, std::pair<unsigned int, unsigned int>> F1>
  __attribute__((pure)) static unsigned int
  gcd_functional(const std::pair<unsigned int, unsigned int> p, F1 &&gcd0) {
    unsigned int n = p.first;
    unsigned int n0 = p.second;
    if (n <= 0) {
      return n0;
    } else {
      unsigned int n1 = n - 1;
      if (n0 <= 0) {
        return (n1 + 1);
      } else {
        unsigned int n2 = n0 - 1;
        return gcd_clause_3(n1, n2, PeanoNat::ltb((n1 + 1), (n2 + 1)), gcd0);
      }
    }
  }

  __attribute__((pure)) static unsigned int
  gcd(const std::pair<unsigned int, unsigned int> x);
  __attribute__((pure)) static unsigned int
  gcd_unfold_clause_3(const unsigned int n, const unsigned int n0,
                      const bool refine);
  __attribute__((pure)) static unsigned int
  gcd_unfold(const std::pair<unsigned int, unsigned int> p);
  struct gcd_graph;
  struct gcd_clause_3_graph;

  struct gcd_graph {
    // TYPES
    struct Gcd_graph_equation_1 {
      unsigned int d_a0;
    };

    struct Gcd_graph_equation_2 {
      unsigned int d_a0;
    };

    struct Gcd_graph_refinement_3 {
      unsigned int d_a0;
      unsigned int d_a1;
      std::shared_ptr<gcd_clause_3_graph> d_a2;
    };

    using variant_t = std::variant<Gcd_graph_equation_1, Gcd_graph_equation_2,
                                   Gcd_graph_refinement_3>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit gcd_graph(Gcd_graph_equation_1 _v) : d_v_(std::move(_v)) {}

    explicit gcd_graph(Gcd_graph_equation_2 _v) : d_v_(std::move(_v)) {}

    explicit gcd_graph(Gcd_graph_refinement_3 _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<gcd_graph> Gcd_graph_equation_1_(unsigned int a0) {
        return std::shared_ptr<gcd_graph>(
            new gcd_graph(Gcd_graph_equation_1{a0}));
      }

      static std::shared_ptr<gcd_graph> Gcd_graph_equation_2_(unsigned int a0) {
        return std::shared_ptr<gcd_graph>(
            new gcd_graph(Gcd_graph_equation_2{a0}));
      }

      static std::shared_ptr<gcd_graph>
      Gcd_graph_refinement_3_(unsigned int a0, unsigned int a1,
                              const std::shared_ptr<gcd_clause_3_graph> &a2) {
        return std::shared_ptr<gcd_graph>(
            new gcd_graph(Gcd_graph_refinement_3{a0, a1, a2}));
      }

      static std::unique_ptr<gcd_graph>
      Gcd_graph_equation_1_uptr(unsigned int a0) {
        return std::unique_ptr<gcd_graph>(
            new gcd_graph(Gcd_graph_equation_1{a0}));
      }

      static std::unique_ptr<gcd_graph>
      Gcd_graph_equation_2_uptr(unsigned int a0) {
        return std::unique_ptr<gcd_graph>(
            new gcd_graph(Gcd_graph_equation_2{a0}));
      }

      static std::unique_ptr<gcd_graph> Gcd_graph_refinement_3_uptr(
          unsigned int a0, unsigned int a1,
          const std::shared_ptr<gcd_clause_3_graph> &a2) {
        return std::unique_ptr<gcd_graph>(
            new gcd_graph(Gcd_graph_refinement_3{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  struct gcd_clause_3_graph {
    // TYPES
    struct Gcd_clause_3_graph_equation_1 {
      unsigned int d_a0;
      unsigned int d_a1;
      std::shared_ptr<gcd_graph> d_a2;
    };

    struct Gcd_clause_3_graph_equation_2 {
      unsigned int d_a0;
      unsigned int d_a1;
      std::shared_ptr<gcd_graph> d_a2;
    };

    using variant_t = std::variant<Gcd_clause_3_graph_equation_1,
                                   Gcd_clause_3_graph_equation_2>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit gcd_clause_3_graph(Gcd_clause_3_graph_equation_1 _v)
        : d_v_(std::move(_v)) {}

    explicit gcd_clause_3_graph(Gcd_clause_3_graph_equation_2 _v)
        : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<gcd_clause_3_graph>
      Gcd_clause_3_graph_equation_1_(unsigned int a0, unsigned int a1,
                                     const std::shared_ptr<gcd_graph> &a2) {
        return std::shared_ptr<gcd_clause_3_graph>(
            new gcd_clause_3_graph(Gcd_clause_3_graph_equation_1{a0, a1, a2}));
      }

      static std::shared_ptr<gcd_clause_3_graph>
      Gcd_clause_3_graph_equation_2_(unsigned int a0, unsigned int a1,
                                     const std::shared_ptr<gcd_graph> &a2) {
        return std::shared_ptr<gcd_clause_3_graph>(
            new gcd_clause_3_graph(Gcd_clause_3_graph_equation_2{a0, a1, a2}));
      }

      static std::unique_ptr<gcd_clause_3_graph>
      Gcd_clause_3_graph_equation_1_uptr(unsigned int a0, unsigned int a1,
                                         const std::shared_ptr<gcd_graph> &a2) {
        return std::unique_ptr<gcd_clause_3_graph>(
            new gcd_clause_3_graph(Gcd_clause_3_graph_equation_1{a0, a1, a2}));
      }

      static std::unique_ptr<gcd_clause_3_graph>
      Gcd_clause_3_graph_equation_2_uptr(unsigned int a0, unsigned int a1,
                                         const std::shared_ptr<gcd_graph> &a2) {
        return std::unique_ptr<gcd_clause_3_graph>(
            new gcd_clause_3_graph(Gcd_clause_3_graph_equation_2{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, typename F2, typename F3, typename F4>
  static T1 gcd_graph_mut(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                          const std::pair<unsigned int, unsigned int> _x0,
                          const unsigned int _x1,
                          std::shared_ptr<gcd_graph> _x2) {
    std::function<T1(std::pair<unsigned int, unsigned int>, unsigned int,
                     std::shared_ptr<gcd_graph>)>
        f5;
    std::function<T2(unsigned int, unsigned int, bool, unsigned int,
                     std::shared_ptr<gcd_clause_3_graph>)>
        f4;
    f5 = [&](std::pair<unsigned int, unsigned int> _x, unsigned int _x3,
             std::shared_ptr<gcd_graph> g) -> T1 {
      return std::visit(
          Overloaded{
              [&](const typename gcd_graph::Gcd_graph_equation_1 _args) -> T1 {
                unsigned int y = _args.d_a0;
                return f(std::move(y));
              },
              [&](const typename gcd_graph::Gcd_graph_equation_2 _args) -> T1 {
                unsigned int n = _args.d_a0;
                return f0(std::move(n));
              },
              [&](const typename gcd_graph::Gcd_graph_refinement_3 _args)
                  -> T1 {
                unsigned int n = _args.d_a0;
                unsigned int n0 = _args.d_a1;
                std::shared_ptr<gcd_clause_3_graph> hind = _args.d_a2;
                return f1(n, n0, hind,
                          f5(n, n0, PeanoNat::ltb((n + 1), (n0 + 1)))(
                              gcd_unfold_clause_3(
                                  n, n0, PeanoNat::ltb((n + 1), (n0 + 1))),
                              hind));
              }},
          g->v());
    };
    f4 = [&](unsigned int _x, unsigned int _x3, bool _x4, unsigned int _x5,
             std::shared_ptr<gcd_clause_3_graph> g) -> T2 {
      return std::visit(
          Overloaded{
              [&](const typename gcd_clause_3_graph::
                      Gcd_clause_3_graph_equation_1 _args) -> T2 {
                unsigned int n = _args.d_a0;
                unsigned int n0 = _args.d_a1;
                std::shared_ptr<gcd_graph> hind = _args.d_a2;
                return f2(
                    n, n0, hind,
                    f4(std::make_pair((n + 1), ((((n0 + 1) - (n + 1)) > (n0 + 1)
                                                     ? 0
                                                     : ((n0 + 1) - (n + 1))))),
                       gcd(std::make_pair((n + 1),
                                          ((((n0 + 1) - (n + 1)) > (n0 + 1)
                                                ? 0
                                                : ((n0 + 1) - (n + 1)))))),
                       hind));
              },
              [&](const typename gcd_clause_3_graph::
                      Gcd_clause_3_graph_equation_2 _args) -> T2 {
                unsigned int n = _args.d_a0;
                unsigned int n0 = _args.d_a1;
                std::shared_ptr<gcd_graph> hind = _args.d_a2;
                return f3(n, n0, hind,
                          f4(std::make_pair(((((n + 1) - (n0 + 1)) > (n + 1)
                                                  ? 0
                                                  : ((n + 1) - (n0 + 1)))),
                                            (n0 + 1)),
                             gcd(std::make_pair(((((n + 1) - (n0 + 1)) > (n + 1)
                                                      ? 0
                                                      : ((n + 1) - (n0 + 1)))),
                                                (n0 + 1))),
                             hind));
              }},
          g->v());
    };
    return f5(_x0, _x1, _x2);
  }

  template <typename T1, typename T2, typename F0, typename F1, typename F2,
            typename F3, typename F4>
  static T2 gcd_clause_3_graph_mut(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                                   const unsigned int _x0,
                                   const unsigned int _x1, const bool _x2,
                                   const unsigned int _x3,
                                   std::shared_ptr<gcd_clause_3_graph> _x4) {
    std::function<T1(std::pair<unsigned int, unsigned int>, unsigned int,
                     std::shared_ptr<gcd_graph>)>
        f5;
    std::function<T2(unsigned int, unsigned int, bool, unsigned int,
                     std::shared_ptr<gcd_clause_3_graph>)>
        f4;
    f5 = [&](std::pair<unsigned int, unsigned int> _x, unsigned int _x5,
             std::shared_ptr<gcd_graph> g) -> T1 {
      return std::visit(
          Overloaded{
              [&](const typename gcd_graph::Gcd_graph_equation_1 _args) -> T1 {
                unsigned int y = _args.d_a0;
                return f(std::move(y));
              },
              [&](const typename gcd_graph::Gcd_graph_equation_2 _args) -> T1 {
                unsigned int n = _args.d_a0;
                return f0(std::move(n));
              },
              [&](const typename gcd_graph::Gcd_graph_refinement_3 _args)
                  -> T1 {
                unsigned int n = _args.d_a0;
                unsigned int n0 = _args.d_a1;
                std::shared_ptr<gcd_clause_3_graph> hind = _args.d_a2;
                return f1(n, n0, hind,
                          f5(n, n0, PeanoNat::ltb((n + 1), (n0 + 1)))(
                              gcd_unfold_clause_3(
                                  n, n0, PeanoNat::ltb((n + 1), (n0 + 1))),
                              hind));
              }},
          g->v());
    };
    f4 = [&](unsigned int _x, unsigned int _x5, bool _x6, unsigned int _x7,
             std::shared_ptr<gcd_clause_3_graph> g) -> T2 {
      return std::visit(
          Overloaded{
              [&](const typename gcd_clause_3_graph::
                      Gcd_clause_3_graph_equation_1 _args) -> T2 {
                unsigned int n = _args.d_a0;
                unsigned int n0 = _args.d_a1;
                std::shared_ptr<gcd_graph> hind = _args.d_a2;
                return f2(
                    n, n0, hind,
                    f4(std::make_pair((n + 1), ((((n0 + 1) - (n + 1)) > (n0 + 1)
                                                     ? 0
                                                     : ((n0 + 1) - (n + 1))))),
                       gcd(std::make_pair((n + 1),
                                          ((((n0 + 1) - (n + 1)) > (n0 + 1)
                                                ? 0
                                                : ((n0 + 1) - (n + 1)))))),
                       hind));
              },
              [&](const typename gcd_clause_3_graph::
                      Gcd_clause_3_graph_equation_2 _args) -> T2 {
                unsigned int n = _args.d_a0;
                unsigned int n0 = _args.d_a1;
                std::shared_ptr<gcd_graph> hind = _args.d_a2;
                return f3(n, n0, hind,
                          f4(std::make_pair(((((n + 1) - (n0 + 1)) > (n + 1)
                                                  ? 0
                                                  : ((n + 1) - (n0 + 1)))),
                                            (n0 + 1)),
                             gcd(std::make_pair(((((n + 1) - (n0 + 1)) > (n + 1)
                                                      ? 0
                                                      : ((n + 1) - (n0 + 1)))),
                                                (n0 + 1))),
                             hind));
              }},
          g->v());
    };
    return f4(_x0, _x1, _x2, _x3, _x4);
  }

  template <typename T1, typename T2, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, typename F2, typename F3, typename F4>
  static T1 gcd_graph_rect(F0 &&_x0, F1 &&_x1, F2 &&_x2, F3 &&_x3, F4 &&_x4,
                           const std::pair<unsigned int, unsigned int> _x5,
                           const unsigned int _x6,
                           const std::shared_ptr<gcd_graph> &_x7) {
    return gcd_graph_mut(_x0, _x1, _x2, _x3, _x4, _x5, _x6, _x7);
  }

  static std::shared_ptr<gcd_graph>
  gcd_graph_correct(const std::pair<unsigned int, unsigned int> x);

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int, unsigned int, T1> F2,
            MapsTo<T1, unsigned int, unsigned int, T1> F3>
  static T1 gcd_elim(F0 &&f, F1 &&f0, F2 &&f2, F3 &&f3,
                     const std::pair<unsigned int, unsigned int> p) {
    return gcd_graph_mut(
        f, f0,
        [=](unsigned int _x, unsigned int _x0,
            std::shared_ptr<gcd_clause_3_graph> _x1, T1 x) mutable {
          unsigned int _x2 = p.first;
          unsigned int _x3 = p.second;
          return x();
        },
        [=](unsigned int n1, unsigned int n2,
            std::shared_ptr<gcd_graph> _x) mutable {
          unsigned int _x0 = p.first;
          unsigned int _x1 = p.second;
          return f2(n1, n2);
        },
        [=](unsigned int n1, unsigned int n2,
            std::shared_ptr<gcd_graph> _x) mutable {
          unsigned int _x0 = p.first;
          unsigned int _x1 = p.second;
          return f3(n1, n2);
        },
        p, gcd(p), gcd_graph_correct(p));
  }

  template <typename F0, typename F1, typename F2, typename F3>
  static std::any
  FunctionalElimination_gcd(F0 &&_x0, F1 &&_x1, F2 &&_x2, F3 &&_x3,
                            const std::pair<unsigned int, unsigned int> _x4) {
    return gcd_elim(_x0, _x1, _x2, _x3, _x4);
  }

  struct FunctionalInduction_gcd {
    using fun_ind_prf_ty = std::function<std::shared_ptr<gcd_graph>(
        std::pair<unsigned int, unsigned int>)>;

    static std::shared_ptr<gcd_graph>
    fun_ind_prf(std::pair<unsigned int, unsigned int> a0) {
      return gcd_graph_correct(a0);
    }
  };

  static_assert(
      FunctionalInduction<
          FunctionalInduction_gcd,
          std::function<unsigned int(std::pair<unsigned int, unsigned int>)>>);

  template <MapsTo<unsigned int, unsigned int> F2>
  __attribute__((pure)) static unsigned int
  collatz_steps_clause_3(const unsigned int n, const bool refine,
                         F2 &&collatz_steps0) {
    if (refine) {
      return (collatz_steps0(PeanoNat::div2(std::move(n))) + 1);
    } else {
      return (collatz_steps0(((3u * std::move(n)) + 1u)) + 1);
    }
  }

  template <MapsTo<unsigned int, unsigned int> F1>
  __attribute__((pure)) static unsigned int
  collatz_steps_functional(const unsigned int n, F1 &&collatz_steps0) {
    if (n <= 0) {
      return 0u;
    } else {
      unsigned int n0 = n - 1;
      if (n0 <= 0) {
        return 0u;
      } else {
        unsigned int n1 = n0 - 1;
        return collatz_steps_clause_3(n1, PeanoNat::even(((n1 + 1) + 1)),
                                      collatz_steps0);
      }
    }
  }

  __attribute__((pure)) static unsigned int collatz_steps(const unsigned int x);
  __attribute__((pure)) static unsigned int
  collatz_steps_unfold_clause_3(const unsigned int n, const bool refine);
  __attribute__((pure)) static unsigned int
  collatz_steps_unfold(const unsigned int n);
  struct collatz_steps_graph;
  struct collatz_steps_clause_3_graph;

  struct collatz_steps_graph {
    // TYPES
    struct Collatz_steps_graph_equation_1 {};

    struct Collatz_steps_graph_equation_2 {};

    struct Collatz_steps_graph_refinement_3 {
      unsigned int d_a0;
      std::shared_ptr<collatz_steps_clause_3_graph> d_a1;
    };

    using variant_t = std::variant<Collatz_steps_graph_equation_1,
                                   Collatz_steps_graph_equation_2,
                                   Collatz_steps_graph_refinement_3>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit collatz_steps_graph(Collatz_steps_graph_equation_1 _v)
        : d_v_(std::move(_v)) {}

    explicit collatz_steps_graph(Collatz_steps_graph_equation_2 _v)
        : d_v_(std::move(_v)) {}

    explicit collatz_steps_graph(Collatz_steps_graph_refinement_3 _v)
        : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<collatz_steps_graph>
      Collatz_steps_graph_equation_1_() {
        return std::shared_ptr<collatz_steps_graph>(
            new collatz_steps_graph(Collatz_steps_graph_equation_1{}));
      }

      static std::shared_ptr<collatz_steps_graph>
      Collatz_steps_graph_equation_2_() {
        return std::shared_ptr<collatz_steps_graph>(
            new collatz_steps_graph(Collatz_steps_graph_equation_2{}));
      }

      static std::shared_ptr<collatz_steps_graph>
      Collatz_steps_graph_refinement_3_(
          unsigned int a0,
          const std::shared_ptr<collatz_steps_clause_3_graph> &a1) {
        return std::shared_ptr<collatz_steps_graph>(
            new collatz_steps_graph(Collatz_steps_graph_refinement_3{a0, a1}));
      }

      static std::unique_ptr<collatz_steps_graph>
      Collatz_steps_graph_equation_1_uptr() {
        return std::unique_ptr<collatz_steps_graph>(
            new collatz_steps_graph(Collatz_steps_graph_equation_1{}));
      }

      static std::unique_ptr<collatz_steps_graph>
      Collatz_steps_graph_equation_2_uptr() {
        return std::unique_ptr<collatz_steps_graph>(
            new collatz_steps_graph(Collatz_steps_graph_equation_2{}));
      }

      static std::unique_ptr<collatz_steps_graph>
      Collatz_steps_graph_refinement_3_uptr(
          unsigned int a0,
          const std::shared_ptr<collatz_steps_clause_3_graph> &a1) {
        return std::unique_ptr<collatz_steps_graph>(
            new collatz_steps_graph(Collatz_steps_graph_refinement_3{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  struct collatz_steps_clause_3_graph {
    // TYPES
    struct Collatz_steps_clause_3_graph_equation_1 {
      unsigned int d_a0;
      std::shared_ptr<collatz_steps_graph> d_a1;
    };

    struct Collatz_steps_clause_3_graph_equation_2 {
      unsigned int d_a0;
      std::shared_ptr<collatz_steps_graph> d_a1;
    };

    using variant_t = std::variant<Collatz_steps_clause_3_graph_equation_1,
                                   Collatz_steps_clause_3_graph_equation_2>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit collatz_steps_clause_3_graph(
        Collatz_steps_clause_3_graph_equation_1 _v)
        : d_v_(std::move(_v)) {}

    explicit collatz_steps_clause_3_graph(
        Collatz_steps_clause_3_graph_equation_2 _v)
        : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<collatz_steps_clause_3_graph>
      Collatz_steps_clause_3_graph_equation_1_(
          unsigned int a0, const std::shared_ptr<collatz_steps_graph> &a1) {
        return std::shared_ptr<collatz_steps_clause_3_graph>(
            new collatz_steps_clause_3_graph(
                Collatz_steps_clause_3_graph_equation_1{a0, a1}));
      }

      static std::shared_ptr<collatz_steps_clause_3_graph>
      Collatz_steps_clause_3_graph_equation_2_(
          unsigned int a0, const std::shared_ptr<collatz_steps_graph> &a1) {
        return std::shared_ptr<collatz_steps_clause_3_graph>(
            new collatz_steps_clause_3_graph(
                Collatz_steps_clause_3_graph_equation_2{a0, a1}));
      }

      static std::unique_ptr<collatz_steps_clause_3_graph>
      Collatz_steps_clause_3_graph_equation_1_uptr(
          unsigned int a0, const std::shared_ptr<collatz_steps_graph> &a1) {
        return std::unique_ptr<collatz_steps_clause_3_graph>(
            new collatz_steps_clause_3_graph(
                Collatz_steps_clause_3_graph_equation_1{a0, a1}));
      }

      static std::unique_ptr<collatz_steps_clause_3_graph>
      Collatz_steps_clause_3_graph_equation_2_uptr(
          unsigned int a0, const std::shared_ptr<collatz_steps_graph> &a1) {
        return std::unique_ptr<collatz_steps_clause_3_graph>(
            new collatz_steps_clause_3_graph(
                Collatz_steps_clause_3_graph_equation_2{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename F2, typename F3, typename F4>
  static T1 collatz_steps_graph_mut(const T1 f, const T1 f0, F2 &&f1, F3 &&f2,
                                    F4 &&f3, const unsigned int _x0,
                                    const unsigned int _x1,
                                    std::shared_ptr<collatz_steps_graph> _x2) {
    std::function<T1(unsigned int, unsigned int,
                     std::shared_ptr<collatz_steps_graph>)>
        f5;
    std::function<T2(unsigned int, bool, unsigned int,
                     std::shared_ptr<collatz_steps_clause_3_graph>)>
        f4;
    f5 = [&](unsigned int _x, unsigned int _x3,
             std::shared_ptr<collatz_steps_graph> c) -> T1 {
      return std::visit(
          Overloaded{
              [&](const typename collatz_steps_graph::
                      Collatz_steps_graph_equation_1 _args) -> T1 { return f; },
              [&](const typename collatz_steps_graph::
                      Collatz_steps_graph_equation_2 _args) -> T1 {
                return f0;
              },
              [&](const typename collatz_steps_graph::
                      Collatz_steps_graph_refinement_3 _args) -> T1 {
                unsigned int n = _args.d_a0;
                std::shared_ptr<collatz_steps_clause_3_graph> hind = _args.d_a1;
                return f1(n, hind,
                          f5(n, PeanoNat::even(((n + 1) + 1)),
                             collatz_steps_unfold_clause_3(
                                 n, PeanoNat::even(((n + 1) + 1))))(hind));
              }},
          c->v());
    };
    f4 = [&](unsigned int _x, bool _x3, unsigned int _x4,
             std::shared_ptr<collatz_steps_clause_3_graph> c) -> T2 {
      return std::visit(
          Overloaded{
              [&](const typename collatz_steps_clause_3_graph::
                      Collatz_steps_clause_3_graph_equation_1 _args) -> T2 {
                unsigned int n = _args.d_a0;
                std::shared_ptr<collatz_steps_graph> hind = _args.d_a1;
                return f2(n, hind,
                          f4(PeanoNat::div2(n),
                             collatz_steps(PeanoNat::div2(n)), hind));
              },
              [&](const typename collatz_steps_clause_3_graph::
                      Collatz_steps_clause_3_graph_equation_2 _args) -> T2 {
                unsigned int n = _args.d_a0;
                std::shared_ptr<collatz_steps_graph> hind = _args.d_a1;
                return f3(
                    n, hind,
                    f4(((3u * n) + 1u), collatz_steps(((3u * n) + 1u)), hind));
              }},
          c->v());
    };
    return f5(_x0, _x1, _x2);
  }

  template <
      typename T1, typename T2,
      MapsTo<T1, unsigned int, std::shared_ptr<collatz_steps_clause_3_graph>,
             T2>
          F2,
      MapsTo<T2, unsigned int, std::shared_ptr<collatz_steps_graph>, T1> F3,
      MapsTo<T2, unsigned int, std::shared_ptr<collatz_steps_graph>, T1> F4>
  static T2 collatz_steps_clause_3_graph_mut(
      const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
      const unsigned int _x0, const bool _x1, const unsigned int _x2,
      std::shared_ptr<collatz_steps_clause_3_graph> _x3) {
    std::function<T1(unsigned int, unsigned int,
                     std::shared_ptr<collatz_steps_graph>)>
        f5;
    std::function<T2(unsigned int, bool, unsigned int,
                     std::shared_ptr<collatz_steps_clause_3_graph>)>
        f4;
    f5 = [&](unsigned int _x, unsigned int _x4,
             std::shared_ptr<collatz_steps_graph> c) -> T1 {
      return std::visit(
          Overloaded{
              [&](const typename collatz_steps_graph::
                      Collatz_steps_graph_equation_1 _args) -> T1 { return f; },
              [&](const typename collatz_steps_graph::
                      Collatz_steps_graph_equation_2 _args) -> T1 {
                return f0;
              },
              [&](const typename collatz_steps_graph::
                      Collatz_steps_graph_refinement_3 _args) -> T1 {
                unsigned int n = _args.d_a0;
                std::shared_ptr<collatz_steps_clause_3_graph> hind = _args.d_a1;
                return f1(n, hind,
                          f5(n, PeanoNat::even(((n + 1) + 1)),
                             collatz_steps_unfold_clause_3(
                                 n, PeanoNat::even(((n + 1) + 1))))(hind));
              }},
          c->v());
    };
    f4 = [&](unsigned int _x, bool _x4, unsigned int _x5,
             std::shared_ptr<collatz_steps_clause_3_graph> c) -> T2 {
      return std::visit(
          Overloaded{
              [&](const typename collatz_steps_clause_3_graph::
                      Collatz_steps_clause_3_graph_equation_1 _args) -> T2 {
                unsigned int n = _args.d_a0;
                std::shared_ptr<collatz_steps_graph> hind = _args.d_a1;
                return f2(n, hind,
                          f4(PeanoNat::div2(n),
                             collatz_steps(PeanoNat::div2(n)), hind));
              },
              [&](const typename collatz_steps_clause_3_graph::
                      Collatz_steps_clause_3_graph_equation_2 _args) -> T2 {
                unsigned int n = _args.d_a0;
                std::shared_ptr<collatz_steps_graph> hind = _args.d_a1;
                return f3(
                    n, hind,
                    f4(((3u * n) + 1u), collatz_steps(((3u * n) + 1u)), hind));
              }},
          c->v());
    };
    return f4(_x0, _x1, _x2, _x3);
  }

  template <typename T1, typename T2, typename F2, typename F3, typename F4>
  static T1
  collatz_steps_graph_rect(const T1 _x0, const T1 _x1, F2 &&_x2, F3 &&_x3,
                           F4 &&_x4, const unsigned int _x5,
                           const unsigned int _x6,
                           const std::shared_ptr<collatz_steps_graph> &_x7) {
    return collatz_steps_graph_mut(_x0, _x1, _x2, _x3, _x4, _x5, _x6, _x7);
  }

  static std::shared_ptr<collatz_steps_graph>
  collatz_steps_graph_correct(const unsigned int x);

  template <typename T1, MapsTo<T1, unsigned int, T1> F2,
            MapsTo<T1, unsigned int, T1> F3>
  static T1 collatz_steps_elim(const T1 f, const T1 f0, F2 &&f2, F3 &&f3,
                               const unsigned int n) {
    return collatz_steps_graph_mut(
        f, f0,
        [](unsigned int _x, std::shared_ptr<collatz_steps_clause_3_graph> _x0,
           T1 x) { return x(); },
        [=](unsigned int n0, std::shared_ptr<collatz_steps_graph> _x) mutable {
          return f2(n0);
        },
        [=](unsigned int n0, std::shared_ptr<collatz_steps_graph> _x) mutable {
          return f3(n0);
        },
        n, collatz_steps(n), collatz_steps_graph_correct(n));
  }

  template <typename F2, typename F3>
  static std::any FunctionalElimination_collatz_steps(const std::any _x0,
                                                      const std::any _x1,
                                                      F2 &&_x2, F3 &&_x3,
                                                      const unsigned int _x4) {
    return collatz_steps_elim(_x0, _x1, _x2, _x3, _x4);
  }

  struct FunctionalInduction_collatz_steps {
    using fun_ind_prf_ty =
        std::function<std::shared_ptr<collatz_steps_graph>(unsigned int)>;

    static std::shared_ptr<collatz_steps_graph> fun_ind_prf(unsigned int a0) {
      return collatz_steps_graph_correct(a0);
    }
  };

  static_assert(FunctionalInduction<FunctionalInduction_collatz_steps,
                                    std::function<unsigned int(unsigned int)>>);
  static inline const unsigned int test_gcd = gcd(std::make_pair(12u, 8u));
  static inline const unsigned int test_collatz = collatz_steps(6u);
};

#endif // INCLUDED_EQUATIONS
