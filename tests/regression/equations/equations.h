#ifndef INCLUDED_EQUATIONS
#define INCLUDED_EQUATIONS

#include <any>
#include <concepts>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct PeanoNat {
  __attribute__((pure)) static bool even(const unsigned int &n);
  __attribute__((pure)) static unsigned int div2(const unsigned int &n);
};

template <typename I, typename
t_A>
concept FunctionalInduction = requires {
  typename I::fun_ind_prf_ty;
} && (requires {
  { I::fun_ind_prf() } -> std::convertible_to<typename I::fun_ind_prf_ty>;
} || requires {
  { I::fun_ind_prf } -> std::convertible_to<typename I::fun_ind_prf_ty>;
});

struct Equations {
  template <MapsTo<unsigned int, std::pair<unsigned int, unsigned int>> F3>
  __attribute__((pure)) static unsigned int
  gcd_clause_3(unsigned int n, unsigned int n0, const bool &refine, F3 &&gcd0) {
    if (refine) {
      return gcd0(std::make_pair(
          (n + 1),
          ((((n0 + 1) - (n + 1)) > (n0 + 1) ? 0 : ((n0 + 1) - (n + 1))))));
    } else {
      return gcd0(std::make_pair(
          ((((n + 1) - (n0 + 1)) > (n + 1) ? 0 : ((n + 1) - (n0 + 1)))),
          (n0 + 1)));
    }
  }

  template <MapsTo<unsigned int, std::pair<unsigned int, unsigned int>> F1>
  __attribute__((pure)) static unsigned int
  gcd_functional(const std::pair<unsigned int, unsigned int> &p, F1 &&gcd0) {
    const unsigned int &n = p.first;
    const unsigned int &n0 = p.second;
    if (n <= 0) {
      return n0;
    } else {
      unsigned int n1 = n - 1;
      if (n0 <= 0) {
        return (n1 + 1);
      } else {
        unsigned int n2 = n0 - 1;
        return gcd_clause_3(n1, n2, (n1 + 1) < (n2 + 1), gcd0);
      }
    }
  }

  __attribute__((pure)) static unsigned int
  gcd(const std::pair<unsigned int, unsigned int> &x);
  __attribute__((pure)) static unsigned int
  gcd_unfold_clause_3(unsigned int n, unsigned int n0, const bool &refine);
  __attribute__((pure)) static unsigned int
  gcd_unfold(const std::pair<unsigned int, unsigned int> &p);
  struct gcd_graph;
  struct gcd_clause_3_graph;

  struct gcd_graph {
    // TYPES
    struct Gcd_graph_equation_1 {
      unsigned int d_y;
    };

    struct Gcd_graph_equation_2 {
      unsigned int d_n;
    };

    struct Gcd_graph_refinement_3 {
      unsigned int d_n;
      unsigned int d_n0;
      std::unique_ptr<gcd_clause_3_graph> d_hind;
    };

    using variant_t = std::variant<Gcd_graph_equation_1, Gcd_graph_equation_2,
                                   Gcd_graph_refinement_3>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    gcd_graph() {}

    explicit gcd_graph(Gcd_graph_equation_1 _v) : d_v_(std::move(_v)) {}

    explicit gcd_graph(Gcd_graph_equation_2 _v) : d_v_(std::move(_v)) {}

    explicit gcd_graph(Gcd_graph_refinement_3 _v) : d_v_(std::move(_v)) {}

    gcd_graph(const gcd_graph &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    gcd_graph(gcd_graph &&_other) : d_v_(std::move(_other.d_v_)) {}

    gcd_graph &operator=(const gcd_graph &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    gcd_graph &operator=(gcd_graph &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) gcd_graph clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Gcd_graph_equation_1>(_sv.v())) {
        const auto &[d_y] = std::get<Gcd_graph_equation_1>(_sv.v());
        return gcd_graph(Gcd_graph_equation_1{d_y});
      } else if (std::holds_alternative<Gcd_graph_equation_2>(_sv.v())) {
        const auto &[d_n] = std::get<Gcd_graph_equation_2>(_sv.v());
        return gcd_graph(Gcd_graph_equation_2{d_n});
      } else {
        const auto &[d_n, d_n0, d_hind] =
            std::get<Gcd_graph_refinement_3>(_sv.v());
        return gcd_graph(Gcd_graph_refinement_3{
            d_n, d_n0,
            d_hind ? std::make_unique<Equations::gcd_clause_3_graph>(
                         d_hind->clone())
                   : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static gcd_graph
    gcd_graph_equation_1(unsigned int y) {
      return gcd_graph(Gcd_graph_equation_1{std::move(y)});
    }

    __attribute__((pure)) static gcd_graph
    gcd_graph_equation_2(unsigned int n) {
      return gcd_graph(Gcd_graph_equation_2{std::move(n)});
    }

    __attribute__((pure)) static gcd_graph
    gcd_graph_refinement_3(unsigned int n, unsigned int n0,
                           const gcd_clause_3_graph &hind) {
      return gcd_graph(
          Gcd_graph_refinement_3{std::move(n), std::move(n0),
                                 std::make_unique<gcd_clause_3_graph>(hind)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  struct gcd_clause_3_graph {
    // TYPES
    struct Gcd_clause_3_graph_equation_1 {
      unsigned int d_n;
      unsigned int d_n0;
      std::unique_ptr<gcd_graph> d_hind;
    };

    struct Gcd_clause_3_graph_equation_2 {
      unsigned int d_n;
      unsigned int d_n0;
      std::unique_ptr<gcd_graph> d_hind;
    };

    using variant_t = std::variant<Gcd_clause_3_graph_equation_1,
                                   Gcd_clause_3_graph_equation_2>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    gcd_clause_3_graph() {}

    explicit gcd_clause_3_graph(Gcd_clause_3_graph_equation_1 _v)
        : d_v_(std::move(_v)) {}

    explicit gcd_clause_3_graph(Gcd_clause_3_graph_equation_2 _v)
        : d_v_(std::move(_v)) {}

    gcd_clause_3_graph(const gcd_clause_3_graph &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    gcd_clause_3_graph(gcd_clause_3_graph &&_other)
        : d_v_(std::move(_other.d_v_)) {}

    gcd_clause_3_graph &operator=(const gcd_clause_3_graph &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    gcd_clause_3_graph &operator=(gcd_clause_3_graph &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) gcd_clause_3_graph clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Gcd_clause_3_graph_equation_1>(_sv.v())) {
        const auto &[d_n, d_n0, d_hind] =
            std::get<Gcd_clause_3_graph_equation_1>(_sv.v());
        return gcd_clause_3_graph(Gcd_clause_3_graph_equation_1{
            d_n, d_n0,
            d_hind ? std::make_unique<Equations::gcd_graph>(d_hind->clone())
                   : nullptr});
      } else {
        const auto &[d_n, d_n0, d_hind] =
            std::get<Gcd_clause_3_graph_equation_2>(_sv.v());
        return gcd_clause_3_graph(Gcd_clause_3_graph_equation_2{
            d_n, d_n0,
            d_hind ? std::make_unique<Equations::gcd_graph>(d_hind->clone())
                   : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static gcd_clause_3_graph
    gcd_clause_3_graph_equation_1(unsigned int n, unsigned int n0,
                                  const gcd_graph &hind) {
      return gcd_clause_3_graph(Gcd_clause_3_graph_equation_1{
          std::move(n), std::move(n0), std::make_unique<gcd_graph>(hind)});
    }

    __attribute__((pure)) static gcd_clause_3_graph
    gcd_clause_3_graph_equation_2(unsigned int n, unsigned int n0,
                                  const gcd_graph &hind) {
      return gcd_clause_3_graph(Gcd_clause_3_graph_equation_2{
          std::move(n), std::move(n0), std::make_unique<gcd_graph>(hind)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2 = void, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, typename F2, typename F3, typename F4>
  static T1 gcd_graph_mut(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                          std::pair<unsigned int, unsigned int> _x0,
                          unsigned int _x1, gcd_graph _x2) {
    std::function<T1(std::pair<unsigned int, unsigned int>, unsigned int,
                     gcd_graph)>
        f4;
    std::function<T2(unsigned int, unsigned int, bool, unsigned int,
                     gcd_clause_3_graph)>
        f5;
    f4 = [&](std::pair<unsigned int, unsigned int>, unsigned int,
             gcd_graph g) -> T1 {
      if (std::holds_alternative<typename gcd_graph::Gcd_graph_equation_1>(
              g.v())) {
        const auto &[d_y] =
            std::get<typename gcd_graph::Gcd_graph_equation_1>(g.v());
        return f(d_y);
      } else if (std::holds_alternative<
                     typename gcd_graph::Gcd_graph_equation_2>(g.v())) {
        const auto &[d_n] =
            std::get<typename gcd_graph::Gcd_graph_equation_2>(g.v());
        return f0(d_n);
      } else {
        const auto &[d_n, d_n0, d_hind] =
            std::get<typename gcd_graph::Gcd_graph_refinement_3>(g.v());
        return f1(d_n, d_n0, *(d_hind),
                  f5(d_n, d_n0, (d_n + 1) < (d_n0 + 1),
                     gcd_unfold_clause_3(d_n, d_n0, (d_n + 1) < (d_n0 + 1)),
                     *(d_hind)));
      }
    };
    f5 = [&](unsigned int, unsigned int, bool, unsigned int,
             gcd_clause_3_graph g) -> T2 {
      if (std::holds_alternative<
              typename gcd_clause_3_graph::Gcd_clause_3_graph_equation_1>(
              g.v())) {
        const auto &[d_n0, d_n00, d_hind0] = std::get<
            typename gcd_clause_3_graph::Gcd_clause_3_graph_equation_1>(g.v());
        return f2(d_n0, d_n00, *(d_hind0),
                  f4(std::make_pair((d_n0 + 1),
                                    ((((d_n00 + 1) - (d_n0 + 1)) > (d_n00 + 1)
                                          ? 0
                                          : ((d_n00 + 1) - (d_n0 + 1))))),
                     gcd(std::make_pair(
                         (d_n0 + 1), ((((d_n00 + 1) - (d_n0 + 1)) > (d_n00 + 1)
                                           ? 0
                                           : ((d_n00 + 1) - (d_n0 + 1)))))),
                     *(d_hind0)));
      } else {
        const auto &[d_n0, d_n00, d_hind0] = std::get<
            typename gcd_clause_3_graph::Gcd_clause_3_graph_equation_2>(g.v());
        return f3(
            d_n0, d_n00, *(d_hind0),
            f4(std::make_pair(((((d_n0 + 1) - (d_n00 + 1)) > (d_n0 + 1)
                                    ? 0
                                    : ((d_n0 + 1) - (d_n00 + 1)))),
                              (d_n00 + 1)),
               gcd(std::make_pair(((((d_n0 + 1) - (d_n00 + 1)) > (d_n0 + 1)
                                        ? 0
                                        : ((d_n0 + 1) - (d_n00 + 1)))),
                                  (d_n00 + 1))),
               *(d_hind0)));
      }
    };
    return f4(_x0, _x1, _x2);
  }

  template <typename T1 = void, typename T2, typename F0, typename F1,
            typename F2, typename F3, typename F4>
  static T2 gcd_clause_3_graph_mut(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                                   unsigned int _x0, unsigned int _x1, bool _x2,
                                   unsigned int _x3, gcd_clause_3_graph _x4) {
    std::function<T1(std::pair<unsigned int, unsigned int>, unsigned int,
                     gcd_graph)>
        f4;
    std::function<T2(unsigned int, unsigned int, bool, unsigned int,
                     gcd_clause_3_graph)>
        f5;
    f4 = [&](std::pair<unsigned int, unsigned int>, unsigned int,
             gcd_graph g) -> T1 {
      if (std::holds_alternative<typename gcd_graph::Gcd_graph_equation_1>(
              g.v())) {
        const auto &[d_y] =
            std::get<typename gcd_graph::Gcd_graph_equation_1>(g.v());
        return f(d_y);
      } else if (std::holds_alternative<
                     typename gcd_graph::Gcd_graph_equation_2>(g.v())) {
        const auto &[d_n] =
            std::get<typename gcd_graph::Gcd_graph_equation_2>(g.v());
        return f0(d_n);
      } else {
        const auto &[d_n, d_n0, d_hind] =
            std::get<typename gcd_graph::Gcd_graph_refinement_3>(g.v());
        return f1(d_n, d_n0, *(d_hind),
                  f5(d_n, d_n0, (d_n + 1) < (d_n0 + 1),
                     gcd_unfold_clause_3(d_n, d_n0, (d_n + 1) < (d_n0 + 1)),
                     *(d_hind)));
      }
    };
    f5 = [&](unsigned int, unsigned int, bool, unsigned int,
             gcd_clause_3_graph g) -> T2 {
      if (std::holds_alternative<
              typename gcd_clause_3_graph::Gcd_clause_3_graph_equation_1>(
              g.v())) {
        const auto &[d_n0, d_n00, d_hind0] = std::get<
            typename gcd_clause_3_graph::Gcd_clause_3_graph_equation_1>(g.v());
        return f2(d_n0, d_n00, *(d_hind0),
                  f4(std::make_pair((d_n0 + 1),
                                    ((((d_n00 + 1) - (d_n0 + 1)) > (d_n00 + 1)
                                          ? 0
                                          : ((d_n00 + 1) - (d_n0 + 1))))),
                     gcd(std::make_pair(
                         (d_n0 + 1), ((((d_n00 + 1) - (d_n0 + 1)) > (d_n00 + 1)
                                           ? 0
                                           : ((d_n00 + 1) - (d_n0 + 1)))))),
                     *(d_hind0)));
      } else {
        const auto &[d_n0, d_n00, d_hind0] = std::get<
            typename gcd_clause_3_graph::Gcd_clause_3_graph_equation_2>(g.v());
        return f3(
            d_n0, d_n00, *(d_hind0),
            f4(std::make_pair(((((d_n0 + 1) - (d_n00 + 1)) > (d_n0 + 1)
                                    ? 0
                                    : ((d_n0 + 1) - (d_n00 + 1)))),
                              (d_n00 + 1)),
               gcd(std::make_pair(((((d_n0 + 1) - (d_n00 + 1)) > (d_n0 + 1)
                                        ? 0
                                        : ((d_n0 + 1) - (d_n00 + 1)))),
                                  (d_n00 + 1))),
               *(d_hind0)));
      }
    };
    return f5(_x0, _x1, _x2, _x3, _x4);
  }

  template <typename T1, typename T2 = void, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, typename F2, typename F3, typename F4>
  static T1 gcd_graph_rect(F0 &&_x0, F1 &&_x1, F2 &&_x2, F3 &&_x3, F4 &&_x4,
                           const std::pair<unsigned int, unsigned int> &_x5,
                           const unsigned int &_x6, const gcd_graph &_x7) {
    return gcd_graph_mut<T1, T2>(_x0, _x1, _x2, _x3, _x4, _x5, _x6, _x7);
  }

  __attribute__((pure)) static gcd_graph
  gcd_graph_correct(const std::pair<unsigned int, unsigned int> &x);

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int, unsigned int, T1> F2,
            MapsTo<T1, unsigned int, unsigned int, T1> F3>
  static T1 gcd_elim(F0 &&f, F1 &&f0, F2 &&f2, F3 &&f3,
                     std::pair<unsigned int, unsigned int> p) {
    return gcd_graph_mut(
        f, f0,
        [=](const unsigned int &, const unsigned int &,
            const gcd_clause_3_graph &, const T1 x) mutable {
          const unsigned int &_x2 = p.first;
          const unsigned int &_x3 = p.second;
          return x;
        },
        [=](const unsigned int &n1, const unsigned int &n2,
            const gcd_graph &) mutable {
          const unsigned int &_x0 = p.first;
          const unsigned int &_x1 = p.second;
          return [=](T1 _pa0) mutable { return f2(n1, n2, _pa0); };
        },
        [=](const unsigned int &n1, const unsigned int &n2,
            const gcd_graph &) mutable {
          const unsigned int &_x0 = p.first;
          const unsigned int &_x1 = p.second;
          return [=](T1 _pa0) mutable { return f3(n1, n2, _pa0); };
        },
        p, gcd(p), gcd_graph_correct(p));
  }

  template <typename F0, typename F1, typename F2, typename F3>
  static std::any
  FunctionalElimination_gcd(F0 &&_x0, F1 &&_x1, F2 &&_x2, F3 &&_x3,
                            const std::pair<unsigned int, unsigned int> &_x4) {
    return gcd_elim<F0>(_x0, _x1, _x2, _x3, _x4);
  }

  struct FunctionalInduction_gcd {
    using fun_ind_prf_ty =
        std::function<gcd_graph(std::pair<unsigned int, unsigned int>)>;

    __attribute__((pure)) static gcd_graph
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
  collatz_steps_clause_3(const unsigned int &n, const bool &refine,
                         F2 &&collatz_steps0) {
    if (refine) {
      return (collatz_steps0(PeanoNat::div2(n)) + 1);
    } else {
      return (collatz_steps0(((3u * n) + 1u)) + 1);
    }
  }

  template <MapsTo<unsigned int, unsigned int> F1>
  __attribute__((pure)) static unsigned int
  collatz_steps_functional(const unsigned int &n, F1 &&collatz_steps0) {
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

  __attribute__((pure)) static unsigned int
  collatz_steps(const unsigned int &x);
  __attribute__((pure)) static unsigned int
  collatz_steps_unfold_clause_3(const unsigned int &n, const bool &refine);
  __attribute__((pure)) static unsigned int
  collatz_steps_unfold(const unsigned int &n);
  struct collatz_steps_graph;
  struct collatz_steps_clause_3_graph;

  struct collatz_steps_graph {
    // TYPES
    struct Collatz_steps_graph_equation_1 {};

    struct Collatz_steps_graph_equation_2 {};

    struct Collatz_steps_graph_refinement_3 {
      unsigned int d_n;
      std::unique_ptr<collatz_steps_clause_3_graph> d_hind;
    };

    using variant_t = std::variant<Collatz_steps_graph_equation_1,
                                   Collatz_steps_graph_equation_2,
                                   Collatz_steps_graph_refinement_3>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    collatz_steps_graph() {}

    explicit collatz_steps_graph(Collatz_steps_graph_equation_1 _v)
        : d_v_(_v) {}

    explicit collatz_steps_graph(Collatz_steps_graph_equation_2 _v)
        : d_v_(_v) {}

    explicit collatz_steps_graph(Collatz_steps_graph_refinement_3 _v)
        : d_v_(std::move(_v)) {}

    collatz_steps_graph(const collatz_steps_graph &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    collatz_steps_graph(collatz_steps_graph &&_other)
        : d_v_(std::move(_other.d_v_)) {}

    collatz_steps_graph &operator=(const collatz_steps_graph &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    collatz_steps_graph &operator=(collatz_steps_graph &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) collatz_steps_graph clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Collatz_steps_graph_equation_1>(_sv.v())) {
        return collatz_steps_graph(Collatz_steps_graph_equation_1{});
      } else if (std::holds_alternative<Collatz_steps_graph_equation_2>(
                     _sv.v())) {
        return collatz_steps_graph(Collatz_steps_graph_equation_2{});
      } else {
        const auto &[d_n, d_hind] =
            std::get<Collatz_steps_graph_refinement_3>(_sv.v());
        return collatz_steps_graph(Collatz_steps_graph_refinement_3{
            d_n,
            d_hind ? std::make_unique<Equations::collatz_steps_clause_3_graph>(
                         d_hind->clone())
                   : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static collatz_steps_graph
    collatz_steps_graph_equation_1() {
      return collatz_steps_graph(Collatz_steps_graph_equation_1{});
    }

    __attribute__((pure)) static collatz_steps_graph
    collatz_steps_graph_equation_2() {
      return collatz_steps_graph(Collatz_steps_graph_equation_2{});
    }

    __attribute__((pure)) static collatz_steps_graph
    collatz_steps_graph_refinement_3(unsigned int n,
                                     const collatz_steps_clause_3_graph &hind) {
      return collatz_steps_graph(Collatz_steps_graph_refinement_3{
          std::move(n), std::make_unique<collatz_steps_clause_3_graph>(hind)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  struct collatz_steps_clause_3_graph {
    // TYPES
    struct Collatz_steps_clause_3_graph_equation_1 {
      unsigned int d_n;
      std::unique_ptr<collatz_steps_graph> d_hind;
    };

    struct Collatz_steps_clause_3_graph_equation_2 {
      unsigned int d_n;
      std::unique_ptr<collatz_steps_graph> d_hind;
    };

    using variant_t = std::variant<Collatz_steps_clause_3_graph_equation_1,
                                   Collatz_steps_clause_3_graph_equation_2>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    collatz_steps_clause_3_graph() {}

    explicit collatz_steps_clause_3_graph(
        Collatz_steps_clause_3_graph_equation_1 _v)
        : d_v_(std::move(_v)) {}

    explicit collatz_steps_clause_3_graph(
        Collatz_steps_clause_3_graph_equation_2 _v)
        : d_v_(std::move(_v)) {}

    collatz_steps_clause_3_graph(const collatz_steps_clause_3_graph &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    collatz_steps_clause_3_graph(collatz_steps_clause_3_graph &&_other)
        : d_v_(std::move(_other.d_v_)) {}

    collatz_steps_clause_3_graph &
    operator=(const collatz_steps_clause_3_graph &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    collatz_steps_clause_3_graph &
    operator=(collatz_steps_clause_3_graph &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) collatz_steps_clause_3_graph clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Collatz_steps_clause_3_graph_equation_1>(
              _sv.v())) {
        const auto &[d_n, d_hind] =
            std::get<Collatz_steps_clause_3_graph_equation_1>(_sv.v());
        return collatz_steps_clause_3_graph(
            Collatz_steps_clause_3_graph_equation_1{
                d_n, d_hind ? std::make_unique<Equations::collatz_steps_graph>(
                                  d_hind->clone())
                            : nullptr});
      } else {
        const auto &[d_n, d_hind] =
            std::get<Collatz_steps_clause_3_graph_equation_2>(_sv.v());
        return collatz_steps_clause_3_graph(
            Collatz_steps_clause_3_graph_equation_2{
                d_n, d_hind ? std::make_unique<Equations::collatz_steps_graph>(
                                  d_hind->clone())
                            : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static collatz_steps_clause_3_graph
    collatz_steps_clause_3_graph_equation_1(unsigned int n,
                                            const collatz_steps_graph &hind) {
      return collatz_steps_clause_3_graph(
          Collatz_steps_clause_3_graph_equation_1{
              std::move(n), std::make_unique<collatz_steps_graph>(hind)});
    }

    __attribute__((pure)) static collatz_steps_clause_3_graph
    collatz_steps_clause_3_graph_equation_2(unsigned int n,
                                            const collatz_steps_graph &hind) {
      return collatz_steps_clause_3_graph(
          Collatz_steps_clause_3_graph_equation_2{
              std::move(n), std::make_unique<collatz_steps_graph>(hind)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2 = void, typename F2, typename F3,
            typename F4>
  static T1 collatz_steps_graph_mut(const T1 f, const T1 f0, F2 &&f1, F3 &&f2,
                                    F4 &&f3, unsigned int _x0, unsigned int _x1,
                                    collatz_steps_graph _x2) {
    std::function<T1(unsigned int, unsigned int, collatz_steps_graph)> f4;
    std::function<T2(unsigned int, bool, unsigned int,
                     collatz_steps_clause_3_graph)>
        f5;
    f4 = [&](unsigned int, unsigned int, collatz_steps_graph c) -> T1 {
      if (std::holds_alternative<
              typename collatz_steps_graph::Collatz_steps_graph_equation_1>(
              c.v())) {
        return f;
      } else if (std::holds_alternative<typename collatz_steps_graph::
                                            Collatz_steps_graph_equation_2>(
                     c.v())) {
        return f0;
      } else {
        const auto &[d_n, d_hind] = std::get<
            typename collatz_steps_graph::Collatz_steps_graph_refinement_3>(
            c.v());
        return f1(d_n, *(d_hind),
                  f5(d_n, PeanoNat::even(((d_n + 1) + 1)),
                     collatz_steps_unfold_clause_3(
                         d_n, PeanoNat::even(((d_n + 1) + 1))),
                     *(d_hind)));
      }
    };
    f5 = [&](unsigned int, bool, unsigned int,
             collatz_steps_clause_3_graph c) -> T2 {
      if (std::holds_alternative<typename collatz_steps_clause_3_graph::
                                     Collatz_steps_clause_3_graph_equation_1>(
              c.v())) {
        const auto &[d_n0, d_hind0] =
            std::get<typename collatz_steps_clause_3_graph::
                         Collatz_steps_clause_3_graph_equation_1>(c.v());
        return f2(d_n0, *(d_hind0),
                  f4(PeanoNat::div2(d_n0), collatz_steps(PeanoNat::div2(d_n0)),
                     *(d_hind0)));
      } else {
        const auto &[d_n0, d_hind0] =
            std::get<typename collatz_steps_clause_3_graph::
                         Collatz_steps_clause_3_graph_equation_2>(c.v());
        return f3(d_n0, *(d_hind0),
                  f4(((3u * d_n0) + 1u), collatz_steps(((3u * d_n0) + 1u)),
                     *(d_hind0)));
      }
    };
    return f4(_x0, _x1, _x2);
  }

  template <typename T1, typename T2,
            MapsTo<T1, unsigned int, collatz_steps_clause_3_graph, T2> F2,
            MapsTo<T2, unsigned int, collatz_steps_graph, T1> F3,
            MapsTo<T2, unsigned int, collatz_steps_graph, T1> F4>
  static T2 collatz_steps_clause_3_graph_mut(const T1 f, const T1 f0, F2 &&f1,
                                             F3 &&f2, F4 &&f3, unsigned int _x0,
                                             bool _x1, unsigned int _x2,
                                             collatz_steps_clause_3_graph _x3) {
    std::function<T1(unsigned int, unsigned int, collatz_steps_graph)> f4;
    std::function<T2(unsigned int, bool, unsigned int,
                     collatz_steps_clause_3_graph)>
        f5;
    f4 = [&](unsigned int, unsigned int, collatz_steps_graph c) -> T1 {
      if (std::holds_alternative<
              typename collatz_steps_graph::Collatz_steps_graph_equation_1>(
              c.v())) {
        return f;
      } else if (std::holds_alternative<typename collatz_steps_graph::
                                            Collatz_steps_graph_equation_2>(
                     c.v())) {
        return f0;
      } else {
        const auto &[d_n, d_hind] = std::get<
            typename collatz_steps_graph::Collatz_steps_graph_refinement_3>(
            c.v());
        return f1(d_n, *(d_hind),
                  f5(d_n, PeanoNat::even(((d_n + 1) + 1)),
                     collatz_steps_unfold_clause_3(
                         d_n, PeanoNat::even(((d_n + 1) + 1))),
                     *(d_hind)));
      }
    };
    f5 = [&](unsigned int, bool, unsigned int,
             collatz_steps_clause_3_graph c) -> T2 {
      if (std::holds_alternative<typename collatz_steps_clause_3_graph::
                                     Collatz_steps_clause_3_graph_equation_1>(
              c.v())) {
        const auto &[d_n0, d_hind0] =
            std::get<typename collatz_steps_clause_3_graph::
                         Collatz_steps_clause_3_graph_equation_1>(c.v());
        return f2(d_n0, *(d_hind0),
                  f4(PeanoNat::div2(d_n0), collatz_steps(PeanoNat::div2(d_n0)),
                     *(d_hind0)));
      } else {
        const auto &[d_n0, d_hind0] =
            std::get<typename collatz_steps_clause_3_graph::
                         Collatz_steps_clause_3_graph_equation_2>(c.v());
        return f3(d_n0, *(d_hind0),
                  f4(((3u * d_n0) + 1u), collatz_steps(((3u * d_n0) + 1u)),
                     *(d_hind0)));
      }
    };
    return f5(_x0, _x1, _x2, _x3);
  }

  template <typename T1, typename T2 = void, typename F2, typename F3,
            typename F4>
  static T1 collatz_steps_graph_rect(const T1 _x0, const T1 _x1, F2 &&_x2,
                                     F3 &&_x3, F4 &&_x4,
                                     const unsigned int &_x5,
                                     const unsigned int &_x6,
                                     const collatz_steps_graph &_x7) {
    return collatz_steps_graph_mut<T1, T2>(_x0, _x1, _x2, _x3, _x4, _x5, _x6,
                                           _x7);
  }

  __attribute__((pure)) static collatz_steps_graph
  collatz_steps_graph_correct(const unsigned int &x);

  template <typename T1, MapsTo<T1, unsigned int, T1> F2,
            MapsTo<T1, unsigned int, T1> F3>
  static T1 collatz_steps_elim(const T1 f, const T1 f0, F2 &&f2, F3 &&f3,
                               const unsigned int &n) {
    return collatz_steps_graph_mut(
        f, f0,
        [](const unsigned int &, const collatz_steps_clause_3_graph &,
           const T1 x) { return x; },
        [=](const unsigned int &n0, const collatz_steps_graph &) mutable {
          return [=](T1 _pa0) mutable { return f2(n0, _pa0); };
        },
        [=](const unsigned int &n0, const collatz_steps_graph &) mutable {
          return [=](T1 _pa0) mutable { return f3(n0, _pa0); };
        },
        n, collatz_steps(n), collatz_steps_graph_correct(n));
  }

  template <typename F2, typename F3>
  static std::any FunctionalElimination_collatz_steps(const std::any _x0,
                                                      const std::any _x1,
                                                      F2 &&_x2, F3 &&_x3,
                                                      const unsigned int &_x4) {
    return collatz_steps_elim<F2>(_x0, _x1, _x2, _x3, _x4);
  }

  struct FunctionalInduction_collatz_steps {
    using fun_ind_prf_ty = std::function<collatz_steps_graph(unsigned int)>;

    __attribute__((pure)) static collatz_steps_graph
    fun_ind_prf(unsigned int a0) {
      return collatz_steps_graph_correct(a0);
    }
  };

  static_assert(FunctionalInduction<FunctionalInduction_collatz_steps,
                                    std::function<unsigned int(unsigned int)>>);
  static inline const unsigned int test_gcd = gcd(std::make_pair(12u, 8u));
  static inline const unsigned int test_collatz = collatz_steps(6u);
};

#endif // INCLUDED_EQUATIONS
