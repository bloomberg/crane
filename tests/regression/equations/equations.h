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
  static bool even(uint64_t n);
  static uint64_t div2(uint64_t n);
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
    requires std::is_invocable_r_v<uint64_t, F3 &,
                                   std::pair<uint64_t, uint64_t> &>
  static uint64_t gcd_clause_3(uint64_t n, uint64_t n0, bool refine,
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
    requires std::is_invocable_r_v<uint64_t, F1 &,
                                   std::pair<uint64_t, uint64_t> &>
  static uint64_t gcd_functional(std::pair<uint64_t, uint64_t> p, F1 &&gcd0) {
    auto [n, n0] = std::move(p);
    if (n <= 0) {
      return n0;
    } else {
      uint64_t n1 = n - 1;
      if (n0 <= 0) {
        return (n1 + 1);
      } else {
        uint64_t n2 = n0 - 1;
        return gcd_clause_3(n1, n2, (n1 + 1) < (n2 + 1), gcd0);
      }
    }
  }

  static uint64_t gcd(const std::pair<uint64_t, uint64_t> &x);
  static uint64_t gcd_unfold_clause_3(uint64_t n, uint64_t n0, bool refine);
  static uint64_t gcd_unfold(std::pair<uint64_t, uint64_t> p);
  struct gcd_graph;
  struct gcd_clause_3_graph;

  struct gcd_graph {
    // TYPES
    struct Gcd_graph_equation_1 {
      uint64_t y;
    };

    struct Gcd_graph_equation_2 {
      uint64_t n;
    };

    struct Gcd_graph_refinement_3 {
      uint64_t n;
      uint64_t n0;
      std::shared_ptr<gcd_clause_3_graph> hind;
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

    static gcd_graph gcd_graph_equation_1(uint64_t y) {
      return gcd_graph(Gcd_graph_equation_1{y});
    }

    static gcd_graph gcd_graph_equation_2(uint64_t n) {
      return gcd_graph(Gcd_graph_equation_2{n});
    }

    static gcd_graph gcd_graph_refinement_3(uint64_t n, uint64_t n0,
                                            gcd_clause_3_graph hind) {
      return gcd_graph(Gcd_graph_refinement_3{
          n, n0, std::make_shared<gcd_clause_3_graph>(std::move(hind))});
    }

    // MANIPULATORS
    ~gcd_graph() {
      std::vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Gcd_graph_refinement_3>(&_v)) {
          if (_alt->hind) {
            _stack.push_back(std::move(_alt->hind));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = std::any_cast<std::shared_ptr<gcd_graph>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp =
                  std::any_cast<std::shared_ptr<gcd_clause_3_graph>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt =
                      std::get_if<typename gcd_clause_3_graph::
                                      Gcd_clause_3_graph_equation_1>(&_pv)) {
                if (_alt->hind) {
                  _stack.push_back(std::move(_alt->hind));
                }
              }
              if (auto *_alt =
                      std::get_if<typename gcd_clause_3_graph::
                                      Gcd_clause_3_graph_equation_2>(&_pv)) {
                if (_alt->hind) {
                  _stack.push_back(std::move(_alt->hind));
                }
              }
            }
          }
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
      uint64_t n;
      uint64_t n0;
      std::shared_ptr<gcd_graph> hind;
    };

    struct Gcd_clause_3_graph_equation_2 {
      uint64_t n;
      uint64_t n0;
      std::shared_ptr<gcd_graph> hind;
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

    static gcd_clause_3_graph
    gcd_clause_3_graph_equation_1(uint64_t n, uint64_t n0, gcd_graph hind) {
      return gcd_clause_3_graph(Gcd_clause_3_graph_equation_1{
          n, n0, std::make_shared<gcd_graph>(std::move(hind))});
    }

    static gcd_clause_3_graph
    gcd_clause_3_graph_equation_2(uint64_t n, uint64_t n0, gcd_graph hind) {
      return gcd_clause_3_graph(Gcd_clause_3_graph_equation_2{
          n, n0, std::make_shared<gcd_graph>(std::move(hind))});
    }

    // MANIPULATORS
    ~gcd_clause_3_graph() {
      std::vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Gcd_clause_3_graph_equation_1>(&_v)) {
          if (_alt->hind) {
            _stack.push_back(std::move(_alt->hind));
          }
        }
        if (auto *_alt = std::get_if<Gcd_clause_3_graph_equation_2>(&_v)) {
          if (_alt->hind) {
            _stack.push_back(std::move(_alt->hind));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp =
                std::any_cast<std::shared_ptr<gcd_clause_3_graph>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = std::any_cast<std::shared_ptr<gcd_graph>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt =
                      std::get_if<typename gcd_graph::Gcd_graph_refinement_3>(
                          &_pv)) {
                if (_alt->hind) {
                  _stack.push_back(std::move(_alt->hind));
                }
              }
            }
          }
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2 = void, typename F0, typename F1,
            typename F2, typename F3, typename F4>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 gcd_graph_mut(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                          std::pair<uint64_t, uint64_t> _x0, uint64_t _x1,
                          gcd_graph _x2) {
    auto f4_impl = [&](auto &_self_f4, auto &_self_f5,
                       const std::pair<uint64_t, uint64_t> &, uint64_t,
                       const gcd_graph &g) -> T1 {
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
    auto f5_impl = [&](auto &_self_f4, auto &_self_f5, uint64_t, uint64_t, bool,
                       uint64_t, const gcd_clause_3_graph &g) -> T2 {
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
    auto f4 = [&](const std::pair<uint64_t, uint64_t> &_x, uint64_t _x3,
                  const gcd_graph &g) -> T1 {
      return f4_impl(f4_impl, f5_impl, _x, _x3, g);
    };
    auto f5 = [&](uint64_t _x, uint64_t _x3, bool _x4, uint64_t _x5,
                  const gcd_clause_3_graph &g) -> T2 {
      return f5_impl(f4_impl, f5_impl, _x, _x3, _x4, _x5, g);
    };
    return f4(_x0, _x1, _x2);
  }

  template <typename T1 = void, typename T2, typename F0, typename F1,
            typename F2, typename F3, typename F4>
  static T2 gcd_clause_3_graph_mut(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                                   uint64_t _x0, uint64_t _x1, bool _x2,
                                   uint64_t _x3, gcd_clause_3_graph _x4) {
    auto f4_impl = [&](auto &_self_f4, auto &_self_f5,
                       const std::pair<uint64_t, uint64_t> &, uint64_t,
                       const gcd_graph &g) -> T1 {
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
    auto f5_impl = [&](auto &_self_f4, auto &_self_f5, uint64_t, uint64_t, bool,
                       uint64_t, const gcd_clause_3_graph &g) -> T2 {
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
    auto f4 = [&](const std::pair<uint64_t, uint64_t> &_x, uint64_t _x5,
                  const gcd_graph &g) -> T1 {
      return f4_impl(f4_impl, f5_impl, _x, _x5, g);
    };
    auto f5 = [&](uint64_t _x, uint64_t _x5, bool _x6, uint64_t _x7,
                  const gcd_clause_3_graph &g) -> T2 {
      return f5_impl(f4_impl, f5_impl, _x, _x5, _x6, _x7, g);
    };
    return f5(_x0, _x1, _x2, _x3, _x4);
  }

  template <typename T1, typename T2 = void, typename F0, typename F1,
            typename F2, typename F3, typename F4>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 gcd_graph_rect(F0 &&_x0, F1 &&_x1, F2 &&_x2, F3 &&_x3, F4 &&_x4,
                           const std::pair<uint64_t, uint64_t> &_x5,
                           uint64_t _x6, const gcd_graph &_x7) {
    return gcd_graph_mut<T1, T2>(_x0, _x1, _x2, _x3, _x4, _x5, _x6, _x7);
  }

  static gcd_graph gcd_graph_correct(std::pair<uint64_t, uint64_t> x);

  template <typename T1, typename F0, typename F1, typename F2, typename F3>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F2 &, uint64_t &, uint64_t &, T1 &> &&
             std::is_invocable_r_v<T1, F3 &, uint64_t &, uint64_t &, T1 &>
  static T1 gcd_elim(F0 &&f, F1 &&f0, F2 &&f2, F3 &&f3,
                     std::pair<uint64_t, uint64_t> p) {
    return gcd_graph_mut(
        f, f0,
        [=](uint64_t, uint64_t, const gcd_clause_3_graph &,
            const T1 &x) mutable {
          const auto &[_x2, _x3] = p;
          return x;
        },
        [=](uint64_t n1, uint64_t n2, const gcd_graph &) mutable {
          const auto &[_x0, _x1] = p;
          return [=](T1 _pa0) mutable { return f2(n1, n2, _pa0); };
        },
        [=](uint64_t n1, uint64_t n2, const gcd_graph &) mutable {
          const auto &[_x0, _x1] = p;
          return [=](T1 _pa0) mutable { return f3(n1, n2, _pa0); };
        },
        p, gcd(p), gcd_graph_correct(p));
  }

  template <typename F0, typename F1, typename F2, typename F3>
  static std::any
  FunctionalElimination_gcd(F0 &&_x0, F1 &&_x1, F2 &&_x2, F3 &&_x3,
                            const std::pair<uint64_t, uint64_t> &_x4) {
    return gcd_elim<F0>(_x0, _x1, _x2, _x3, _x4);
  }

  struct FunctionalInduction_gcd {
    using fun_ind_prf_ty =
        std::function<gcd_graph(std::pair<uint64_t, uint64_t>)>;

    static gcd_graph fun_ind_prf(std::pair<uint64_t, uint64_t> a0) {
      return gcd_graph_correct(a0);
    }
  };

  static_assert(FunctionalInduction<
                FunctionalInduction_gcd,
                std::function<uint64_t(std::pair<uint64_t, uint64_t>)>>);

  template <typename F2>
    requires std::is_invocable_r_v<uint64_t, F2 &, uint64_t &>
  static uint64_t collatz_steps_clause_3(uint64_t n, bool refine,
                                         F2 &&collatz_steps0) {
    if (refine) {
      return (collatz_steps0(PeanoNat::div2(n)) + 1);
    } else {
      return (collatz_steps0(((UINT64_C(3) * n) + UINT64_C(1))) + 1);
    }
  }

  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static uint64_t collatz_steps_functional(uint64_t n, F1 &&collatz_steps0) {
    if (n <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t n0 = n - 1;
      if (n0 <= 0) {
        return UINT64_C(0);
      } else {
        uint64_t n1 = n0 - 1;
        return collatz_steps_clause_3(n1, PeanoNat::even(((n1 + 1) + 1)),
                                      collatz_steps0);
      }
    }
  }

  static uint64_t collatz_steps(uint64_t x);
  static uint64_t collatz_steps_unfold_clause_3(uint64_t n, bool refine);
  static uint64_t collatz_steps_unfold(uint64_t n);
  struct collatz_steps_graph;
  struct collatz_steps_clause_3_graph;

  struct collatz_steps_graph {
    // TYPES
    struct Collatz_steps_graph_equation_1 {};

    struct Collatz_steps_graph_equation_2 {};

    struct Collatz_steps_graph_refinement_3 {
      uint64_t n;
      std::shared_ptr<collatz_steps_clause_3_graph> hind;
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

    static collatz_steps_graph collatz_steps_graph_equation_1() {
      return collatz_steps_graph(Collatz_steps_graph_equation_1{});
    }

    static collatz_steps_graph collatz_steps_graph_equation_2() {
      return collatz_steps_graph(Collatz_steps_graph_equation_2{});
    }

    static collatz_steps_graph
    collatz_steps_graph_refinement_3(uint64_t n,
                                     collatz_steps_clause_3_graph hind) {
      return collatz_steps_graph(Collatz_steps_graph_refinement_3{
          n, std::make_shared<collatz_steps_clause_3_graph>(std::move(hind))});
    }

    // MANIPULATORS
    ~collatz_steps_graph() {
      std::vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Collatz_steps_graph_refinement_3>(&_v)) {
          if (_alt->hind) {
            _stack.push_back(std::move(_alt->hind));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp =
                std::any_cast<std::shared_ptr<collatz_steps_graph>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp =
                  std::any_cast<std::shared_ptr<collatz_steps_clause_3_graph>>(
                      &_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt =
                      std::get_if<typename collatz_steps_clause_3_graph::
                                      Collatz_steps_clause_3_graph_equation_1>(
                          &_pv)) {
                if (_alt->hind) {
                  _stack.push_back(std::move(_alt->hind));
                }
              }
              if (auto *_alt =
                      std::get_if<typename collatz_steps_clause_3_graph::
                                      Collatz_steps_clause_3_graph_equation_2>(
                          &_pv)) {
                if (_alt->hind) {
                  _stack.push_back(std::move(_alt->hind));
                }
              }
            }
          }
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
      uint64_t n;
      std::shared_ptr<collatz_steps_graph> hind;
    };

    struct Collatz_steps_clause_3_graph_equation_2 {
      uint64_t n;
      std::shared_ptr<collatz_steps_graph> hind;
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

    static collatz_steps_clause_3_graph
    collatz_steps_clause_3_graph_equation_1(uint64_t n,
                                            collatz_steps_graph hind) {
      return collatz_steps_clause_3_graph(
          Collatz_steps_clause_3_graph_equation_1{
              n, std::make_shared<collatz_steps_graph>(std::move(hind))});
    }

    static collatz_steps_clause_3_graph
    collatz_steps_clause_3_graph_equation_2(uint64_t n,
                                            collatz_steps_graph hind) {
      return collatz_steps_clause_3_graph(
          Collatz_steps_clause_3_graph_equation_2{
              n, std::make_shared<collatz_steps_graph>(std::move(hind))});
    }

    // MANIPULATORS
    ~collatz_steps_clause_3_graph() {
      std::vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt =
                std::get_if<Collatz_steps_clause_3_graph_equation_1>(&_v)) {
          if (_alt->hind) {
            _stack.push_back(std::move(_alt->hind));
          }
        }
        if (auto *_alt =
                std::get_if<Collatz_steps_clause_3_graph_equation_2>(&_v)) {
          if (_alt->hind) {
            _stack.push_back(std::move(_alt->hind));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp =
                std::any_cast<std::shared_ptr<collatz_steps_clause_3_graph>>(
                    &_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp =
                  std::any_cast<std::shared_ptr<collatz_steps_graph>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt =
                      std::get_if<typename collatz_steps_graph::
                                      Collatz_steps_graph_refinement_3>(&_pv)) {
                if (_alt->hind) {
                  _stack.push_back(std::move(_alt->hind));
                }
              }
            }
          }
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
                                    F4 &&f3, uint64_t _x0, uint64_t _x1,
                                    collatz_steps_graph _x2) {
    auto f4_impl = [&](auto &_self_f4, auto &_self_f5, uint64_t, uint64_t,
                       const collatz_steps_graph &c) -> T1 {
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
    auto f5_impl = [&](auto &_self_f4, auto &_self_f5, uint64_t, bool, uint64_t,
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
                  _self_f4(_self_f4, _self_f5,
                           ((UINT64_C(3) * n0) + UINT64_C(1)),
                           collatz_steps(((UINT64_C(3) * n0) + UINT64_C(1))),
                           *hind0));
      }
    };
    auto f4 = [&](uint64_t _x, uint64_t _x3,
                  const collatz_steps_graph &c) -> T1 {
      return f4_impl(f4_impl, f5_impl, _x, _x3, c);
    };
    auto f5 = [&](uint64_t _x, bool _x3, uint64_t _x4,
                  const collatz_steps_clause_3_graph &c) -> T2 {
      return f5_impl(f4_impl, f5_impl, _x, _x3, _x4, c);
    };
    return f4(_x0, _x1, _x2);
  }

  template <typename T1, typename T2, typename F2, typename F3, typename F4>
    requires std::is_invocable_r_v<T1, F2 &, uint64_t &,
                                   collatz_steps_clause_3_graph &, T2 &> &&
             std::is_invocable_r_v<T2, F3 &, uint64_t &, collatz_steps_graph &,
                                   T1 &> &&
             std::is_invocable_r_v<T2, F4 &, uint64_t &, collatz_steps_graph &,
                                   T1 &>
  static T2 collatz_steps_clause_3_graph_mut(const T1 &f, const T1 &f0, F2 &&f1,
                                             F3 &&f2, F4 &&f3, uint64_t _x0,
                                             bool _x1, uint64_t _x2,
                                             collatz_steps_clause_3_graph _x3) {
    auto f4_impl = [&](auto &_self_f4, auto &_self_f5, uint64_t, uint64_t,
                       const collatz_steps_graph &c) -> T1 {
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
    auto f5_impl = [&](auto &_self_f4, auto &_self_f5, uint64_t, bool, uint64_t,
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
                  _self_f4(_self_f4, _self_f5,
                           ((UINT64_C(3) * n0) + UINT64_C(1)),
                           collatz_steps(((UINT64_C(3) * n0) + UINT64_C(1))),
                           *hind0));
      }
    };
    auto f4 = [&](uint64_t _x, uint64_t _x4,
                  const collatz_steps_graph &c) -> T1 {
      return f4_impl(f4_impl, f5_impl, _x, _x4, c);
    };
    auto f5 = [&](uint64_t _x, bool _x4, uint64_t _x5,
                  const collatz_steps_clause_3_graph &c) -> T2 {
      return f5_impl(f4_impl, f5_impl, _x, _x4, _x5, c);
    };
    return f5(_x0, _x1, _x2, _x3);
  }

  template <typename T1, typename T2 = void, typename F2, typename F3,
            typename F4>
  static T1 collatz_steps_graph_rect(const T1 &_x0, const T1 &_x1, F2 &&_x2,
                                     F3 &&_x3, F4 &&_x4, uint64_t _x5,
                                     uint64_t _x6,
                                     const collatz_steps_graph &_x7) {
    return collatz_steps_graph_mut<T1, T2>(_x0, _x1, _x2, _x3, _x4, _x5, _x6,
                                           _x7);
  }

  static collatz_steps_graph collatz_steps_graph_correct(uint64_t x);

  template <typename T1, typename F2, typename F3>
    requires std::is_invocable_r_v<T1, F2 &, uint64_t &, T1 &> &&
             std::is_invocable_r_v<T1, F3 &, uint64_t &, T1 &>
  static T1 collatz_steps_elim(const T1 &f, const T1 &f0, F2 &&f2, F3 &&f3,
                               uint64_t n) {
    return collatz_steps_graph_mut(
        f, f0,
        [](uint64_t, const collatz_steps_clause_3_graph &, const T1 &x) {
          return x;
        },
        [=](uint64_t n0, const collatz_steps_graph &) mutable {
          return [=](T1 _pa0) mutable { return f2(n0, _pa0); };
        },
        [=](uint64_t n0, const collatz_steps_graph &) mutable {
          return [=](T1 _pa0) mutable { return f3(n0, _pa0); };
        },
        n, collatz_steps(n), collatz_steps_graph_correct(n));
  }

  template <typename F2, typename F3>
  static std::any FunctionalElimination_collatz_steps(std::any _x0,
                                                      std::any _x1, F2 &&_x2,
                                                      F3 &&_x3, uint64_t _x4) {
    return collatz_steps_elim<F2>(_x0, _x1, _x2, _x3, _x4);
  }

  struct FunctionalInduction_collatz_steps {
    using fun_ind_prf_ty = std::function<collatz_steps_graph(uint64_t)>;

    static collatz_steps_graph fun_ind_prf(uint64_t a0) {
      return collatz_steps_graph_correct(a0);
    }
  };

  static_assert(FunctionalInduction<FunctionalInduction_collatz_steps,
                                    std::function<uint64_t(uint64_t)>>);
  static inline const uint64_t test_gcd =
      gcd(std::make_pair(UINT64_C(12), UINT64_C(8)));
  static inline const uint64_t test_collatz = collatz_steps(UINT64_C(6));
};

#endif // INCLUDED_EQUATIONS
