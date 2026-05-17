#ifndef INCLUDED_EQUATIONS
#define INCLUDED_EQUATIONS

#include <any>
#include <concepts>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct PeanoNat {
  static bool even(unsigned int n);
  static unsigned int div2(unsigned int n);
};

template <typename I, typename
A>concept FunctionalInduction = requires {
  typename I::fun_ind_prf_ty;
} && (requires {
  { I::fun_ind_prf() } -> std::convertible_to<typename I::fun_ind_prf_ty>;
} || requires {
  { I::fun_ind_prf } -> std::convertible_to<typename I::fun_ind_prf_ty>;
});

struct Equations {
  template <typename F3>
    requires std::is_invocable_r_v<unsigned int, F3 &,
                                   std::pair<unsigned int, unsigned int> &>
  static unsigned int gcd_clause_3(unsigned int n, unsigned int n0, bool refine,
                                   F3 &&gcd0) {
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

  template <typename F1>
    requires std::is_invocable_r_v<unsigned int, F1 &,
                                   std::pair<unsigned int, unsigned int> &>
  static unsigned int
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

  static unsigned int gcd(const std::pair<unsigned int, unsigned int> &x);
  static unsigned int gcd_unfold_clause_3(unsigned int n, unsigned int n0,
                                          bool refine);
  static unsigned int
  gcd_unfold(const std::pair<unsigned int, unsigned int> &p);
  struct gcd_graph;
  struct gcd_clause_3_graph;

  struct gcd_graph {
    // TYPES
    struct Gcd_graph_equation_1 {
      unsigned int y;
    };

    struct Gcd_graph_equation_2 {
      unsigned int n;
    };

    struct Gcd_graph_refinement_3 {
      unsigned int n;
      unsigned int n0;
      std::unique_ptr<gcd_clause_3_graph> hind;
    };

    using variant_t = std::variant<Gcd_graph_equation_1, Gcd_graph_equation_2,
                                   Gcd_graph_refinement_3>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    gcd_graph() {}

    explicit gcd_graph(Gcd_graph_equation_1 _v) : v_(std::move(_v)) {}

    explicit gcd_graph(Gcd_graph_equation_2 _v) : v_(std::move(_v)) {}

    explicit gcd_graph(Gcd_graph_refinement_3 _v) : v_(std::move(_v)) {}

    gcd_graph(const gcd_graph &_other) : v_(std::move(_other.clone().v_)) {}

    gcd_graph(gcd_graph &&_other) : v_(std::move(_other.v_)) {}

    gcd_graph &operator=(const gcd_graph &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    gcd_graph &operator=(gcd_graph &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    gcd_graph clone() const {
      if (std::holds_alternative<Gcd_graph_equation_1>(this->v())) {
        const auto &[y] = std::get<Gcd_graph_equation_1>(this->v());
        return gcd_graph(Gcd_graph_equation_1{y});
      } else if (std::holds_alternative<Gcd_graph_equation_2>(this->v())) {
        const auto &[n] = std::get<Gcd_graph_equation_2>(this->v());
        return gcd_graph(Gcd_graph_equation_2{n});
      } else {
        const auto &[n, n0, hind] = std::get<Gcd_graph_refinement_3>(this->v());
        return gcd_graph(Gcd_graph_refinement_3{
            n, n0,
            hind
                ? std::make_unique<Equations::gcd_clause_3_graph>(hind->clone())
                : nullptr});
      }
    }

    // CREATORS
    static gcd_graph gcd_graph_equation_1(unsigned int y) {
      return gcd_graph(Gcd_graph_equation_1{y});
    }

    static gcd_graph gcd_graph_equation_2(unsigned int n) {
      return gcd_graph(Gcd_graph_equation_2{n});
    }

    static gcd_graph gcd_graph_refinement_3(unsigned int n, unsigned int n0,
                                            gcd_clause_3_graph hind) {
      return gcd_graph(Gcd_graph_refinement_3{
          n, n0, std::make_unique<gcd_clause_3_graph>(std::move(hind))});
    }

    // MANIPULATORS
    ~gcd_graph() {
      std::vector<std::unique_ptr<gcd_graph>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](gcd_graph &_node) {
        if (std::holds_alternative<Gcd_graph_refinement_3>(_node.v_)) {
          auto &_alt = std::get<Gcd_graph_refinement_3>(_node.v_);
          if (_alt.hind) {
            if (std::holds_alternative<typename Equations::gcd_clause_3_graph::
                                           Gcd_clause_3_graph_equation_1>(
                    _alt.hind->v())) {
              auto &_palt = std::get<typename Equations::gcd_clause_3_graph::
                                         Gcd_clause_3_graph_equation_1>(
                  _alt.hind->v_mut());
              if (_palt.hind) {
                _stack.push_back(std::move(_palt.hind));
              }
            }
            if (std::holds_alternative<typename Equations::gcd_clause_3_graph::
                                           Gcd_clause_3_graph_equation_2>(
                    _alt.hind->v())) {
              auto &_palt = std::get<typename Equations::gcd_clause_3_graph::
                                         Gcd_clause_3_graph_equation_2>(
                  _alt.hind->v_mut());
              if (_palt.hind) {
                _stack.push_back(std::move(_palt.hind));
              }
            }
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct gcd_clause_3_graph {
    // TYPES
    struct Gcd_clause_3_graph_equation_1 {
      unsigned int n;
      unsigned int n0;
      std::unique_ptr<gcd_graph> hind;
    };

    struct Gcd_clause_3_graph_equation_2 {
      unsigned int n;
      unsigned int n0;
      std::unique_ptr<gcd_graph> hind;
    };

    using variant_t = std::variant<Gcd_clause_3_graph_equation_1,
                                   Gcd_clause_3_graph_equation_2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    gcd_clause_3_graph() {}

    explicit gcd_clause_3_graph(Gcd_clause_3_graph_equation_1 _v)
        : v_(std::move(_v)) {}

    explicit gcd_clause_3_graph(Gcd_clause_3_graph_equation_2 _v)
        : v_(std::move(_v)) {}

    gcd_clause_3_graph(const gcd_clause_3_graph &_other)
        : v_(std::move(_other.clone().v_)) {}

    gcd_clause_3_graph(gcd_clause_3_graph &&_other)
        : v_(std::move(_other.v_)) {}

    gcd_clause_3_graph &operator=(const gcd_clause_3_graph &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    gcd_clause_3_graph &operator=(gcd_clause_3_graph &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    gcd_clause_3_graph clone() const {
      if (std::holds_alternative<Gcd_clause_3_graph_equation_1>(this->v())) {
        const auto &[n, n0, hind] =
            std::get<Gcd_clause_3_graph_equation_1>(this->v());
        return gcd_clause_3_graph(Gcd_clause_3_graph_equation_1{
            n, n0,
            hind ? std::make_unique<Equations::gcd_graph>(hind->clone())
                 : nullptr});
      } else {
        const auto &[n, n0, hind] =
            std::get<Gcd_clause_3_graph_equation_2>(this->v());
        return gcd_clause_3_graph(Gcd_clause_3_graph_equation_2{
            n, n0,
            hind ? std::make_unique<Equations::gcd_graph>(hind->clone())
                 : nullptr});
      }
    }

    // CREATORS
    static gcd_clause_3_graph gcd_clause_3_graph_equation_1(unsigned int n,
                                                            unsigned int n0,
                                                            gcd_graph hind) {
      return gcd_clause_3_graph(Gcd_clause_3_graph_equation_1{
          n, n0, std::make_unique<gcd_graph>(std::move(hind))});
    }

    static gcd_clause_3_graph gcd_clause_3_graph_equation_2(unsigned int n,
                                                            unsigned int n0,
                                                            gcd_graph hind) {
      return gcd_clause_3_graph(Gcd_clause_3_graph_equation_2{
          n, n0, std::make_unique<gcd_graph>(std::move(hind))});
    }

    // MANIPULATORS
    ~gcd_clause_3_graph() {
      std::vector<std::unique_ptr<gcd_clause_3_graph>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](gcd_clause_3_graph &_node) {
        if (std::holds_alternative<Gcd_clause_3_graph_equation_1>(_node.v_)) {
          auto &_alt = std::get<Gcd_clause_3_graph_equation_1>(_node.v_);
          if (_alt.hind) {
            if (std::holds_alternative<
                    typename Equations::gcd_graph::Gcd_graph_refinement_3>(
                    _alt.hind->v())) {
              auto &_palt = std::get<
                  typename Equations::gcd_graph::Gcd_graph_refinement_3>(
                  _alt.hind->v_mut());
              if (_palt.hind) {
                _stack.push_back(std::move(_palt.hind));
              }
            }
          }
        }
        if (std::holds_alternative<Gcd_clause_3_graph_equation_2>(_node.v_)) {
          auto &_alt = std::get<Gcd_clause_3_graph_equation_2>(_node.v_);
          if (_alt.hind) {
            if (std::holds_alternative<
                    typename Equations::gcd_graph::Gcd_graph_refinement_3>(
                    _alt.hind->v())) {
              auto &_palt = std::get<
                  typename Equations::gcd_graph::Gcd_graph_refinement_3>(
                  _alt.hind->v_mut());
              if (_palt.hind) {
                _stack.push_back(std::move(_palt.hind));
              }
            }
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2 = void, typename F0, typename F1,
            typename F2, typename F3, typename F4>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &>
  static T1 gcd_graph_mut(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                          std::pair<unsigned int, unsigned int> _x0,
                          unsigned int _x1, gcd_graph _x2) {
    auto f4_impl = [&](auto &_self_f4, auto &_self_f5,
                       const std::pair<unsigned int, unsigned int> &,
                       unsigned int, const gcd_graph &g) -> T1 {
      if (std::holds_alternative<typename gcd_graph::Gcd_graph_equation_1>(
              g.v())) {
        const auto &[y0] =
            std::get<typename gcd_graph::Gcd_graph_equation_1>(g.v());
        return f(y0);
      } else if (std::holds_alternative<
                     typename gcd_graph::Gcd_graph_equation_2>(g.v())) {
        const auto &[n0] =
            std::get<typename gcd_graph::Gcd_graph_equation_2>(g.v());
        return f0(n0);
      } else {
        const auto &[n1, n2, hind0] =
            std::get<typename gcd_graph::Gcd_graph_refinement_3>(g.v());
        return f1(n1, n2, *hind0,
                  _self_f5(_self_f4, _self_f5, n1, n2, (n1 + 1) < (n2 + 1),
                           gcd_unfold_clause_3(n1, n2, (n1 + 1) < (n2 + 1)),
                           *hind0));
      }
    };
    auto f5_impl = [&](auto &_self_f4, auto &_self_f5, unsigned int,
                       unsigned int, bool, unsigned int,
                       const gcd_clause_3_graph &g) -> T2 {
      if (std::holds_alternative<
              typename gcd_clause_3_graph::Gcd_clause_3_graph_equation_1>(
              g.v())) {
        const auto &[n1, n00, hind0] = std::get<
            typename gcd_clause_3_graph::Gcd_clause_3_graph_equation_1>(g.v());
        return f2(n1, n00, *hind0,
                  _self_f4(_self_f4, _self_f5,
                           std::make_pair((n1 + 1),
                                          ((((n00 + 1) - (n1 + 1)) > (n00 + 1)
                                                ? 0
                                                : ((n00 + 1) - (n1 + 1))))),
                           gcd(std::make_pair(
                               (n1 + 1), ((((n00 + 1) - (n1 + 1)) > (n00 + 1)
                                               ? 0
                                               : ((n00 + 1) - (n1 + 1)))))),
                           *hind0));
      } else {
        const auto &[n1, n00, hind0] = std::get<
            typename gcd_clause_3_graph::Gcd_clause_3_graph_equation_2>(g.v());
        return f3(
            n1, n00, *hind0,
            _self_f4(_self_f4, _self_f5,
                     std::make_pair(((((n1 + 1) - (n00 + 1)) > (n1 + 1)
                                          ? 0
                                          : ((n1 + 1) - (n00 + 1)))),
                                    (n00 + 1)),
                     gcd(std::make_pair(((((n1 + 1) - (n00 + 1)) > (n1 + 1)
                                              ? 0
                                              : ((n1 + 1) - (n00 + 1)))),
                                        (n00 + 1))),
                     *hind0));
      }
    };
    auto f4 = [&](const std::pair<unsigned int, unsigned int> &_x,
                  unsigned int _x3, const gcd_graph &g) -> T1 {
      return f4_impl(f4_impl, f5_impl, _x, _x3, g);
    };
    auto f5 = [&](unsigned int _x, unsigned int _x3, bool _x4, unsigned int _x5,
                  const gcd_clause_3_graph &g) -> T2 {
      return f5_impl(f4_impl, f5_impl, _x, _x3, _x4, _x5, g);
    };
    return f4(_x0, _x1, _x2);
  }

  template <typename T1 = void, typename T2, typename F0, typename F1,
            typename F2, typename F3, typename F4>
  static T2 gcd_clause_3_graph_mut(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                                   unsigned int _x0, unsigned int _x1, bool _x2,
                                   unsigned int _x3, gcd_clause_3_graph _x4) {
    auto f4_impl = [&](auto &_self_f4, auto &_self_f5,
                       const std::pair<unsigned int, unsigned int> &,
                       unsigned int, const gcd_graph &g) -> T1 {
      if (std::holds_alternative<typename gcd_graph::Gcd_graph_equation_1>(
              g.v())) {
        const auto &[y0] =
            std::get<typename gcd_graph::Gcd_graph_equation_1>(g.v());
        return f(y0);
      } else if (std::holds_alternative<
                     typename gcd_graph::Gcd_graph_equation_2>(g.v())) {
        const auto &[n0] =
            std::get<typename gcd_graph::Gcd_graph_equation_2>(g.v());
        return f0(n0);
      } else {
        const auto &[n1, n2, hind0] =
            std::get<typename gcd_graph::Gcd_graph_refinement_3>(g.v());
        return f1(n1, n2, *hind0,
                  _self_f5(_self_f4, _self_f5, n1, n2, (n1 + 1) < (n2 + 1),
                           gcd_unfold_clause_3(n1, n2, (n1 + 1) < (n2 + 1)),
                           *hind0));
      }
    };
    auto f5_impl = [&](auto &_self_f4, auto &_self_f5, unsigned int,
                       unsigned int, bool, unsigned int,
                       const gcd_clause_3_graph &g) -> T2 {
      if (std::holds_alternative<
              typename gcd_clause_3_graph::Gcd_clause_3_graph_equation_1>(
              g.v())) {
        const auto &[n1, n00, hind0] = std::get<
            typename gcd_clause_3_graph::Gcd_clause_3_graph_equation_1>(g.v());
        return f2(n1, n00, *hind0,
                  _self_f4(_self_f4, _self_f5,
                           std::make_pair((n1 + 1),
                                          ((((n00 + 1) - (n1 + 1)) > (n00 + 1)
                                                ? 0
                                                : ((n00 + 1) - (n1 + 1))))),
                           gcd(std::make_pair(
                               (n1 + 1), ((((n00 + 1) - (n1 + 1)) > (n00 + 1)
                                               ? 0
                                               : ((n00 + 1) - (n1 + 1)))))),
                           *hind0));
      } else {
        const auto &[n1, n00, hind0] = std::get<
            typename gcd_clause_3_graph::Gcd_clause_3_graph_equation_2>(g.v());
        return f3(
            n1, n00, *hind0,
            _self_f4(_self_f4, _self_f5,
                     std::make_pair(((((n1 + 1) - (n00 + 1)) > (n1 + 1)
                                          ? 0
                                          : ((n1 + 1) - (n00 + 1)))),
                                    (n00 + 1)),
                     gcd(std::make_pair(((((n1 + 1) - (n00 + 1)) > (n1 + 1)
                                              ? 0
                                              : ((n1 + 1) - (n00 + 1)))),
                                        (n00 + 1))),
                     *hind0));
      }
    };
    auto f4 = [&](const std::pair<unsigned int, unsigned int> &_x,
                  unsigned int _x5, const gcd_graph &g) -> T1 {
      return f4_impl(f4_impl, f5_impl, _x, _x5, g);
    };
    auto f5 = [&](unsigned int _x, unsigned int _x5, bool _x6, unsigned int _x7,
                  const gcd_clause_3_graph &g) -> T2 {
      return f5_impl(f4_impl, f5_impl, _x, _x5, _x6, _x7, g);
    };
    return f5(_x0, _x1, _x2, _x3, _x4);
  }

  template <typename T1, typename T2 = void, typename F0, typename F1,
            typename F2, typename F3, typename F4>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &>
  static T1 gcd_graph_rect(F0 &&_x0, F1 &&_x1, F2 &&_x2, F3 &&_x3, F4 &&_x4,
                           const std::pair<unsigned int, unsigned int> &_x5,
                           unsigned int _x6, const gcd_graph &_x7) {
    return gcd_graph_mut<T1, T2>(_x0, _x1, _x2, _x3, _x4, _x5, _x6, _x7);
  }

  static gcd_graph
  gcd_graph_correct(const std::pair<unsigned int, unsigned int> &x);

  template <typename T1, typename F0, typename F1, typename F2, typename F3>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F2 &, unsigned int &, unsigned int &,
                                   T1 &> &&
             std::is_invocable_r_v<T1, F3 &, unsigned int &, unsigned int &,
                                   T1 &>
  static T1 gcd_elim(F0 &&f, F1 &&f0, F2 &&f2, F3 &&f3,
                     std::pair<unsigned int, unsigned int> p) {
    return gcd_graph_mut(
        f, f0,
        [=](unsigned int, unsigned int, const gcd_clause_3_graph &,
            const T1 &x) mutable {
          const unsigned int &_x2 = p.first;
          const unsigned int &_x3 = p.second;
          return x;
        },
        [=](unsigned int n1, unsigned int n2, const gcd_graph &) mutable {
          const unsigned int &_x0 = p.first;
          const unsigned int &_x1 = p.second;
          return [=](T1 _pa0) mutable { return f2(n1, n2, _pa0); };
        },
        [=](unsigned int n1, unsigned int n2, const gcd_graph &) mutable {
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

    static gcd_graph fun_ind_prf(std::pair<unsigned int, unsigned int> a0) {
      return gcd_graph_correct(a0);
    }
  };

  static_assert(
      FunctionalInduction<
          FunctionalInduction_gcd,
          std::function<unsigned int(std::pair<unsigned int, unsigned int>)>>);

  template <typename F2>
    requires std::is_invocable_r_v<unsigned int, F2 &, unsigned int &>
  static unsigned int collatz_steps_clause_3(unsigned int n, bool refine,
                                             F2 &&collatz_steps0) {
    if (refine) {
      return (collatz_steps0(PeanoNat::div2(n)) + 1);
    } else {
      return (collatz_steps0(((3u * n) + 1u)) + 1);
    }
  }

  template <typename F1>
    requires std::is_invocable_r_v<unsigned int, F1 &, unsigned int &>
  static unsigned int collatz_steps_functional(unsigned int n,
                                               F1 &&collatz_steps0) {
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

  static unsigned int collatz_steps(unsigned int x);
  static unsigned int collatz_steps_unfold_clause_3(unsigned int n,
                                                    bool refine);
  static unsigned int collatz_steps_unfold(unsigned int n);
  struct collatz_steps_graph;
  struct collatz_steps_clause_3_graph;

  struct collatz_steps_graph {
    // TYPES
    struct Collatz_steps_graph_equation_1 {};

    struct Collatz_steps_graph_equation_2 {};

    struct Collatz_steps_graph_refinement_3 {
      unsigned int n;
      std::unique_ptr<collatz_steps_clause_3_graph> hind;
    };

    using variant_t = std::variant<Collatz_steps_graph_equation_1,
                                   Collatz_steps_graph_equation_2,
                                   Collatz_steps_graph_refinement_3>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    collatz_steps_graph() {}

    explicit collatz_steps_graph(Collatz_steps_graph_equation_1 _v) : v_(_v) {}

    explicit collatz_steps_graph(Collatz_steps_graph_equation_2 _v) : v_(_v) {}

    explicit collatz_steps_graph(Collatz_steps_graph_refinement_3 _v)
        : v_(std::move(_v)) {}

    collatz_steps_graph(const collatz_steps_graph &_other)
        : v_(std::move(_other.clone().v_)) {}

    collatz_steps_graph(collatz_steps_graph &&_other)
        : v_(std::move(_other.v_)) {}

    collatz_steps_graph &operator=(const collatz_steps_graph &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    collatz_steps_graph &operator=(collatz_steps_graph &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    collatz_steps_graph clone() const {
      if (std::holds_alternative<Collatz_steps_graph_equation_1>(this->v())) {
        return collatz_steps_graph(Collatz_steps_graph_equation_1{});
      } else if (std::holds_alternative<Collatz_steps_graph_equation_2>(
                     this->v())) {
        return collatz_steps_graph(Collatz_steps_graph_equation_2{});
      } else {
        const auto &[n, hind] =
            std::get<Collatz_steps_graph_refinement_3>(this->v());
        return collatz_steps_graph(Collatz_steps_graph_refinement_3{
            n, hind ? std::make_unique<Equations::collatz_steps_clause_3_graph>(
                          hind->clone())
                    : nullptr});
      }
    }

    // CREATORS
    static collatz_steps_graph collatz_steps_graph_equation_1() {
      return collatz_steps_graph(Collatz_steps_graph_equation_1{});
    }

    static collatz_steps_graph collatz_steps_graph_equation_2() {
      return collatz_steps_graph(Collatz_steps_graph_equation_2{});
    }

    static collatz_steps_graph
    collatz_steps_graph_refinement_3(unsigned int n,
                                     collatz_steps_clause_3_graph hind) {
      return collatz_steps_graph(Collatz_steps_graph_refinement_3{
          n, std::make_unique<collatz_steps_clause_3_graph>(std::move(hind))});
    }

    // MANIPULATORS
    ~collatz_steps_graph() {
      std::vector<std::unique_ptr<collatz_steps_graph>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](collatz_steps_graph &_node) {
        if (std::holds_alternative<Collatz_steps_graph_refinement_3>(
                _node.v_)) {
          auto &_alt = std::get<Collatz_steps_graph_refinement_3>(_node.v_);
          if (_alt.hind) {
            if (std::holds_alternative<
                    typename Equations::collatz_steps_clause_3_graph::
                        Collatz_steps_clause_3_graph_equation_1>(
                    _alt.hind->v())) {
              auto &_palt =
                  std::get<typename Equations::collatz_steps_clause_3_graph::
                               Collatz_steps_clause_3_graph_equation_1>(
                      _alt.hind->v_mut());
              if (_palt.hind) {
                _stack.push_back(std::move(_palt.hind));
              }
            }
            if (std::holds_alternative<
                    typename Equations::collatz_steps_clause_3_graph::
                        Collatz_steps_clause_3_graph_equation_2>(
                    _alt.hind->v())) {
              auto &_palt =
                  std::get<typename Equations::collatz_steps_clause_3_graph::
                               Collatz_steps_clause_3_graph_equation_2>(
                      _alt.hind->v_mut());
              if (_palt.hind) {
                _stack.push_back(std::move(_palt.hind));
              }
            }
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct collatz_steps_clause_3_graph {
    // TYPES
    struct Collatz_steps_clause_3_graph_equation_1 {
      unsigned int n;
      std::unique_ptr<collatz_steps_graph> hind;
    };

    struct Collatz_steps_clause_3_graph_equation_2 {
      unsigned int n;
      std::unique_ptr<collatz_steps_graph> hind;
    };

    using variant_t = std::variant<Collatz_steps_clause_3_graph_equation_1,
                                   Collatz_steps_clause_3_graph_equation_2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    collatz_steps_clause_3_graph() {}

    explicit collatz_steps_clause_3_graph(
        Collatz_steps_clause_3_graph_equation_1 _v)
        : v_(std::move(_v)) {}

    explicit collatz_steps_clause_3_graph(
        Collatz_steps_clause_3_graph_equation_2 _v)
        : v_(std::move(_v)) {}

    collatz_steps_clause_3_graph(const collatz_steps_clause_3_graph &_other)
        : v_(std::move(_other.clone().v_)) {}

    collatz_steps_clause_3_graph(collatz_steps_clause_3_graph &&_other)
        : v_(std::move(_other.v_)) {}

    collatz_steps_clause_3_graph &
    operator=(const collatz_steps_clause_3_graph &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    collatz_steps_clause_3_graph &
    operator=(collatz_steps_clause_3_graph &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    collatz_steps_clause_3_graph clone() const {
      if (std::holds_alternative<Collatz_steps_clause_3_graph_equation_1>(
              this->v())) {
        const auto &[n, hind] =
            std::get<Collatz_steps_clause_3_graph_equation_1>(this->v());
        return collatz_steps_clause_3_graph(
            Collatz_steps_clause_3_graph_equation_1{
                n, hind ? std::make_unique<Equations::collatz_steps_graph>(
                              hind->clone())
                        : nullptr});
      } else {
        const auto &[n, hind] =
            std::get<Collatz_steps_clause_3_graph_equation_2>(this->v());
        return collatz_steps_clause_3_graph(
            Collatz_steps_clause_3_graph_equation_2{
                n, hind ? std::make_unique<Equations::collatz_steps_graph>(
                              hind->clone())
                        : nullptr});
      }
    }

    // CREATORS
    static collatz_steps_clause_3_graph
    collatz_steps_clause_3_graph_equation_1(unsigned int n,
                                            collatz_steps_graph hind) {
      return collatz_steps_clause_3_graph(
          Collatz_steps_clause_3_graph_equation_1{
              n, std::make_unique<collatz_steps_graph>(std::move(hind))});
    }

    static collatz_steps_clause_3_graph
    collatz_steps_clause_3_graph_equation_2(unsigned int n,
                                            collatz_steps_graph hind) {
      return collatz_steps_clause_3_graph(
          Collatz_steps_clause_3_graph_equation_2{
              n, std::make_unique<collatz_steps_graph>(std::move(hind))});
    }

    // MANIPULATORS
    ~collatz_steps_clause_3_graph() {
      std::vector<std::unique_ptr<collatz_steps_clause_3_graph>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](collatz_steps_clause_3_graph &_node) {
        if (std::holds_alternative<Collatz_steps_clause_3_graph_equation_1>(
                _node.v_)) {
          auto &_alt =
              std::get<Collatz_steps_clause_3_graph_equation_1>(_node.v_);
          if (_alt.hind) {
            if (std::holds_alternative<typename Equations::collatz_steps_graph::
                                           Collatz_steps_graph_refinement_3>(
                    _alt.hind->v())) {
              auto &_palt = std::get<typename Equations::collatz_steps_graph::
                                         Collatz_steps_graph_refinement_3>(
                  _alt.hind->v_mut());
              if (_palt.hind) {
                _stack.push_back(std::move(_palt.hind));
              }
            }
          }
        }
        if (std::holds_alternative<Collatz_steps_clause_3_graph_equation_2>(
                _node.v_)) {
          auto &_alt =
              std::get<Collatz_steps_clause_3_graph_equation_2>(_node.v_);
          if (_alt.hind) {
            if (std::holds_alternative<typename Equations::collatz_steps_graph::
                                           Collatz_steps_graph_refinement_3>(
                    _alt.hind->v())) {
              auto &_palt = std::get<typename Equations::collatz_steps_graph::
                                         Collatz_steps_graph_refinement_3>(
                  _alt.hind->v_mut());
              if (_palt.hind) {
                _stack.push_back(std::move(_palt.hind));
              }
            }
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2 = void, typename F2, typename F3,
            typename F4>
  static T1 collatz_steps_graph_mut(const T1 &f, const T1 &f0, F2 &&f1, F3 &&f2,
                                    F4 &&f3, unsigned int _x0, unsigned int _x1,
                                    collatz_steps_graph _x2) {
    auto f4_impl = [&](auto &_self_f4, auto &_self_f5, unsigned int,
                       unsigned int, const collatz_steps_graph &c) -> T1 {
      if (std::holds_alternative<
              typename collatz_steps_graph::Collatz_steps_graph_equation_1>(
              c.v())) {
        return f;
      } else if (std::holds_alternative<typename collatz_steps_graph::
                                            Collatz_steps_graph_equation_2>(
                     c.v())) {
        return f0;
      } else {
        const auto &[n0, hind0] = std::get<
            typename collatz_steps_graph::Collatz_steps_graph_refinement_3>(
            c.v());
        return f1(n0, *hind0,
                  _self_f5(_self_f4, _self_f5, n0,
                           PeanoNat::even(((n0 + 1) + 1)),
                           collatz_steps_unfold_clause_3(
                               n0, PeanoNat::even(((n0 + 1) + 1))),
                           *hind0));
      }
    };
    auto f5_impl = [&](auto &_self_f4, auto &_self_f5, unsigned int, bool,
                       unsigned int,
                       const collatz_steps_clause_3_graph &c) -> T2 {
      if (std::holds_alternative<typename collatz_steps_clause_3_graph::
                                     Collatz_steps_clause_3_graph_equation_1>(
              c.v())) {
        const auto &[n0, hind0] =
            std::get<typename collatz_steps_clause_3_graph::
                         Collatz_steps_clause_3_graph_equation_1>(c.v());
        return f2(n0, *hind0,
                  _self_f4(_self_f4, _self_f5, PeanoNat::div2(n0),
                           collatz_steps(PeanoNat::div2(n0)), *hind0));
      } else {
        const auto &[n0, hind0] =
            std::get<typename collatz_steps_clause_3_graph::
                         Collatz_steps_clause_3_graph_equation_2>(c.v());
        return f3(n0, *hind0,
                  _self_f4(_self_f4, _self_f5, ((3u * n0) + 1u),
                           collatz_steps(((3u * n0) + 1u)), *hind0));
      }
    };
    auto f4 = [&](unsigned int _x, unsigned int _x3,
                  const collatz_steps_graph &c) -> T1 {
      return f4_impl(f4_impl, f5_impl, _x, _x3, c);
    };
    auto f5 = [&](unsigned int _x, bool _x3, unsigned int _x4,
                  const collatz_steps_clause_3_graph &c) -> T2 {
      return f5_impl(f4_impl, f5_impl, _x, _x3, _x4, c);
    };
    return f4(_x0, _x1, _x2);
  }

  template <typename T1, typename T2, typename F2, typename F3, typename F4>
    requires std::is_invocable_r_v<T1, F2 &, unsigned int &,
                                   collatz_steps_clause_3_graph &, T2 &> &&
             std::is_invocable_r_v<T2, F3 &, unsigned int &,
                                   collatz_steps_graph &, T1 &> &&
             std::is_invocable_r_v<T2, F4 &, unsigned int &,
                                   collatz_steps_graph &, T1 &>
  static T2 collatz_steps_clause_3_graph_mut(const T1 &f, const T1 &f0, F2 &&f1,
                                             F3 &&f2, F4 &&f3, unsigned int _x0,
                                             bool _x1, unsigned int _x2,
                                             collatz_steps_clause_3_graph _x3) {
    auto f4_impl = [&](auto &_self_f4, auto &_self_f5, unsigned int,
                       unsigned int, const collatz_steps_graph &c) -> T1 {
      if (std::holds_alternative<
              typename collatz_steps_graph::Collatz_steps_graph_equation_1>(
              c.v())) {
        return f;
      } else if (std::holds_alternative<typename collatz_steps_graph::
                                            Collatz_steps_graph_equation_2>(
                     c.v())) {
        return f0;
      } else {
        const auto &[n0, hind0] = std::get<
            typename collatz_steps_graph::Collatz_steps_graph_refinement_3>(
            c.v());
        return f1(n0, *hind0,
                  _self_f5(_self_f4, _self_f5, n0,
                           PeanoNat::even(((n0 + 1) + 1)),
                           collatz_steps_unfold_clause_3(
                               n0, PeanoNat::even(((n0 + 1) + 1))),
                           *hind0));
      }
    };
    auto f5_impl = [&](auto &_self_f4, auto &_self_f5, unsigned int, bool,
                       unsigned int,
                       const collatz_steps_clause_3_graph &c) -> T2 {
      if (std::holds_alternative<typename collatz_steps_clause_3_graph::
                                     Collatz_steps_clause_3_graph_equation_1>(
              c.v())) {
        const auto &[n0, hind0] =
            std::get<typename collatz_steps_clause_3_graph::
                         Collatz_steps_clause_3_graph_equation_1>(c.v());
        return f2(n0, *hind0,
                  _self_f4(_self_f4, _self_f5, PeanoNat::div2(n0),
                           collatz_steps(PeanoNat::div2(n0)), *hind0));
      } else {
        const auto &[n0, hind0] =
            std::get<typename collatz_steps_clause_3_graph::
                         Collatz_steps_clause_3_graph_equation_2>(c.v());
        return f3(n0, *hind0,
                  _self_f4(_self_f4, _self_f5, ((3u * n0) + 1u),
                           collatz_steps(((3u * n0) + 1u)), *hind0));
      }
    };
    auto f4 = [&](unsigned int _x, unsigned int _x4,
                  const collatz_steps_graph &c) -> T1 {
      return f4_impl(f4_impl, f5_impl, _x, _x4, c);
    };
    auto f5 = [&](unsigned int _x, bool _x4, unsigned int _x5,
                  const collatz_steps_clause_3_graph &c) -> T2 {
      return f5_impl(f4_impl, f5_impl, _x, _x4, _x5, c);
    };
    return f5(_x0, _x1, _x2, _x3);
  }

  template <typename T1, typename T2 = void, typename F2, typename F3,
            typename F4>
  static T1 collatz_steps_graph_rect(const T1 &_x0, const T1 &_x1, F2 &&_x2,
                                     F3 &&_x3, F4 &&_x4, unsigned int _x5,
                                     unsigned int _x6,
                                     const collatz_steps_graph &_x7) {
    return collatz_steps_graph_mut<T1, T2>(_x0, _x1, _x2, _x3, _x4, _x5, _x6,
                                           _x7);
  }

  static collatz_steps_graph collatz_steps_graph_correct(unsigned int x);

  template <typename T1, typename F2, typename F3>
    requires std::is_invocable_r_v<T1, F2 &, unsigned int &, T1 &> &&
             std::is_invocable_r_v<T1, F3 &, unsigned int &, T1 &>
  static T1 collatz_steps_elim(const T1 &f, const T1 &f0, F2 &&f2, F3 &&f3,
                               unsigned int n) {
    return collatz_steps_graph_mut(
        f, f0,
        [](unsigned int, const collatz_steps_clause_3_graph &, const T1 &x) {
          return x;
        },
        [=](unsigned int n0, const collatz_steps_graph &) mutable {
          return [=](T1 _pa0) mutable { return f2(n0, _pa0); };
        },
        [=](unsigned int n0, const collatz_steps_graph &) mutable {
          return [=](T1 _pa0) mutable { return f3(n0, _pa0); };
        },
        n, collatz_steps(n), collatz_steps_graph_correct(n));
  }

  template <typename F2, typename F3>
  static std::any
  FunctionalElimination_collatz_steps(std::any _x0, std::any _x1, F2 &&_x2,
                                      F3 &&_x3, unsigned int _x4) {
    return collatz_steps_elim<F2>(_x0, _x1, _x2, _x3, _x4);
  }

  struct FunctionalInduction_collatz_steps {
    using fun_ind_prf_ty = std::function<collatz_steps_graph(unsigned int)>;

    static collatz_steps_graph fun_ind_prf(unsigned int a0) {
      return collatz_steps_graph_correct(a0);
    }
  };

  static_assert(FunctionalInduction<FunctionalInduction_collatz_steps,
                                    std::function<unsigned int(unsigned int)>>);
  static inline const unsigned int test_gcd = gcd(std::make_pair(12u, 8u));
  static inline const unsigned int test_collatz = collatz_steps(6u);
};

#endif // INCLUDED_EQUATIONS
