#ifndef INCLUDED_WF_FIX_SIGMA_DOMAIN
#define INCLUDED_WF_FIX_SIGMA_DOMAIN

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A, typename B> struct sigma;
template <typename I, typename
A>concept FunctionalInduction = requires {
    typename I::fun_ind_prf_ty;
  } && (requires {
    { I::fun_ind_prf() } -> std::convertible_to<typename I::fun_ind_prf_ty>;
  } || requires {
    { I::fun_ind_prf } -> std::convertible_to<typename I::fun_ind_prf_ty>;
  });

template <typename A, typename B> struct sigma {
  A pr1;
  B pr2;

  // ACCESSORS
  template <typename CraneU0, typename CraneU1>
  operator sigma<CraneU0, CraneU1>() const {
    return {[&]() -> CraneU0 {
              if constexpr (crane_convertible<CraneU0, const A &>) {
                return crane_convert<CraneU0>(pr1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const B &>) {
                return crane_convert<CraneU1>(pr2);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }
};

struct WfFixSigmaDomain {
  template <typename F2>
  static uint64_t sw_functional(uint64_t a, uint64_t b, F2 &&sw0) {
    if (a <= 0) {
      return b;
    } else {
      uint64_t n = a - 1;
      return (sw0(b, n) + 1);
    }
  }

  template <typename T1> static uint64_t sw_crane_Fix_F(const T1 x) {
    return sw_functional(x.pr1, x.pr2, [](uint64_t a0, uint64_t b0) {
      T1 y = sigma<uint64_t, uint64_t>{a0, b0};
      return sw_crane_Fix_F<T1>(y);
    });
  }

  static uint64_t sw(uint64_t a, uint64_t b);
  static uint64_t sw_unfold(uint64_t a, uint64_t b);

  struct sw_graph {
    // TYPES
    struct Sw_graph_equation_1 {
      uint64_t b;
    };

    struct Sw_graph_equation_2 {
      uint64_t a;
      uint64_t b;
      std::shared_ptr<sw_graph> hind;
    };

    using variant_t = std::variant<Sw_graph_equation_1, Sw_graph_equation_2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    sw_graph() {}

    explicit sw_graph(Sw_graph_equation_1 _v) : v_(std::move(_v)) {}

    explicit sw_graph(Sw_graph_equation_2 _v) : v_(std::move(_v)) {}

    static sw_graph sw_graph_equation_1(uint64_t b) {
      return sw_graph(Sw_graph_equation_1{b});
    }

    static sw_graph sw_graph_equation_2(uint64_t a, uint64_t b, sw_graph hind) {
      return sw_graph(Sw_graph_equation_2{
          a, b, std::make_shared<sw_graph>(std::move(hind))});
    }

    // MANIPULATORS
    ~sw_graph() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<sw_graph> {
        if (auto *_alt = std::get_if<Sw_graph_equation_2>(&_v)) {
          if (_alt->hind && _alt->hind.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->hind);
          }
        }
        return nullptr;
      };
      std::shared_ptr<sw_graph> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    sw_graph(const sw_graph &) = default;
    sw_graph &operator=(const sw_graph &) = default;
    sw_graph(sw_graph &&) = default;
    sw_graph &operator=(sw_graph &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  static T1 sw_graph_rect(F0 &&f, F1 &&f0, uint64_t, uint64_t, uint64_t,
                          const sw_graph &s) {
    if (std::holds_alternative<typename sw_graph::Sw_graph_equation_1>(s.v())) {
      const auto &[b0] =
          std::get<typename sw_graph::Sw_graph_equation_1>(s.v());
      return f(b0);
    } else {
      const auto &[a0, b0, hind0] =
          std::get<typename sw_graph::Sw_graph_equation_2>(s.v());
      return f0(a0, b0, *hind0,
                sw_graph_rect<T1>(f, f0, b0, a0, sw(b0, a0), *hind0));
    }
  }

  template <typename T1>
  static uint64_t sw_graph_correct_crane_Fix_F(const T1 x) {
    uint64_t x0 = x.pr2;
    crane::fn<sw_graph(uint64_t, uint64_t)> h = [](uint64_t a0, uint64_t b0) {
      T1 y = sigma<uint64_t, uint64_t>{a0, b0};
      return sw_graph_correct_crane_Fix_F<T1>(y);
    };
    if (x.pr1 <= 0) {
      return sw_graph::sw_graph_equation_1(x0);
    } else {
      uint64_t n = x.pr1 - 1;
      return sw_graph::sw_graph_equation_2(n, x0, h(x0, n));
    }
  }

  static sw_graph sw_graph_correct(uint64_t a, uint64_t b);

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, const uint64_t &, const uint64_t &,
                                   T1>
  static T1 sw_elim(F0 &&f, F1 &&f0, uint64_t a, uint64_t b) {
    auto f1_impl = [&](auto &_self_f1, uint64_t, uint64_t, uint64_t,
                       const sw_graph &s) -> T1 {
      if (std::holds_alternative<typename sw_graph::Sw_graph_equation_1>(
              s.v())) {
        const auto &[b1] =
            std::get<typename sw_graph::Sw_graph_equation_1>(s.v());
        return f(b1);
      } else {
        const auto &[a1, b1, hind0] =
            std::get<typename sw_graph::Sw_graph_equation_2>(s.v());
        return f0(a1, b1, _self_f1(_self_f1, b1, a1, sw(b1, a1), *hind0));
      }
    };
    {
      uint64_t _lc1_x = a;
      uint64_t _lc1_x0 = b;
      uint64_t _lc1_x1 = sw(a, b);
      const sw_graph &_lc1_s = sw_graph_correct(a, b);
      return f1_impl(f1_impl, _lc1_x, _lc1_x0, _lc1_x1, _lc1_s);
    }
  }

  template <typename F0, typename F1>
  static crane::obj FunctionalElimination_sw(F0 &&x0_, F1 &&x1_, uint64_t x2_,
                                             uint64_t x3_) {
    return sw_elim(x0_, x1_, x2_, x3_);
  }

  struct FunctionalInduction_sw {
    using fun_ind_prf_ty = crane::fn<sw_graph(uint64_t, uint64_t)>;

    static crane::fn<sw_graph(uint64_t, uint64_t)> fun_ind_prf() {
      return sw_graph_correct;
    }
  };

  static_assert(FunctionalInduction<FunctionalInduction_sw,
                                    crane::fn<uint64_t(uint64_t, uint64_t)>>);
  static inline const uint64_t result = sw(UINT64_C(3), UINT64_C(4));
};

#endif // INCLUDED_WF_FIX_SIGMA_DOMAIN
