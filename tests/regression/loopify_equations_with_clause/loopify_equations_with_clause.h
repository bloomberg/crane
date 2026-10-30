#ifndef INCLUDED_LOOPIFY_EQUATIONS_WITH_CLAUSE
#define INCLUDED_LOOPIFY_EQUATIONS_WITH_CLAUSE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename I, typename
A>concept FunctionalInduction = requires {
    typename I::fun_ind_prf_ty;
  } && (requires {
    { I::fun_ind_prf() } -> std::convertible_to<typename I::fun_ind_prf_ty>;
  } || requires {
    { I::fun_ind_prf } -> std::convertible_to<typename I::fun_ind_prf_ty>;
  });

struct Nat {};

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct LoopifyEquationsWithClause {
  template <typename F3>
  static uint64_t zeros_clause_2(uint64_t, bool refine,
                                 const List<uint64_t> &xs, F3 &&zeros0) {
    if (refine) {
      return (zeros0(xs) + 1);
    } else {
      return zeros0(xs);
    }
  }

  template <typename F1>
  static uint64_t zeros_functional(const List<uint64_t> &l, F1 &&zeros0) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      return zeros_clause_2(a0, a0 == UINT64_C(0), *a1, zeros0);
    }
  }

  static uint64_t zeros(const List<uint64_t> &x);
  static uint64_t zeros_unfold_clause_2(uint64_t _x, bool refine,
                                        const List<uint64_t> &xs);
  static uint64_t zeros_unfold(const List<uint64_t> &l);
  struct zeros_graph;
  struct zeros_clause_2_graph;

  struct zeros_graph {
    // TYPES
    struct Zeros_graph_equation_1 {};

    struct Zeros_graph_refinement_2 {
      uint64_t x;
      List<uint64_t> xs;
      std::shared_ptr<zeros_clause_2_graph> hind;
    };

    using variant_t =
        std::variant<Zeros_graph_equation_1, Zeros_graph_refinement_2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    zeros_graph() {}

    explicit zeros_graph(Zeros_graph_equation_1 _v) : v_(_v) {}

    explicit zeros_graph(Zeros_graph_refinement_2 _v) : v_(std::move(_v)) {}

    static zeros_graph zeros_graph_equation_1() {
      return zeros_graph(Zeros_graph_equation_1{});
    }

    static zeros_graph zeros_graph_refinement_2(uint64_t x, List<uint64_t> xs,
                                                zeros_clause_2_graph hind) {
      return zeros_graph(Zeros_graph_refinement_2{
          x, std::move(xs),
          std::make_shared<zeros_clause_2_graph>(std::move(hind))});
    }

    // MANIPULATORS
    ~zeros_graph() {
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Zeros_graph_refinement_2>(&_v)) {
          if (_alt->hind && _alt->hind.use_count() == 1) {
            _stack.push_back(std::move(_alt->hind));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = crane::any_cast<std::shared_ptr<zeros_graph>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp =
                  crane::any_cast<std::shared_ptr<zeros_clause_2_graph>>(
                      &_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt =
                      std::get_if<typename zeros_clause_2_graph::
                                      Zeros_clause_2_graph_equation_1>(&_pv)) {
                if (_alt->hind && _alt->hind.use_count() == 1) {
                  _stack.push_back(std::move(_alt->hind));
                }
              }
              if (auto *_alt =
                      std::get_if<typename zeros_clause_2_graph::
                                      Zeros_clause_2_graph_equation_2>(&_pv)) {
                if (_alt->hind && _alt->hind.use_count() == 1) {
                  _stack.push_back(std::move(_alt->hind));
                }
              }
            }
          }
        }
      }
    }

    zeros_graph(const zeros_graph &) = default;
    zeros_graph &operator=(const zeros_graph &) = default;
    zeros_graph(zeros_graph &&) = default;
    zeros_graph &operator=(zeros_graph &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct zeros_clause_2_graph {
    // TYPES
    struct Zeros_clause_2_graph_equation_1 {
      uint64_t x;
      List<uint64_t> xs;
      std::shared_ptr<zeros_graph> hind;
    };

    struct Zeros_clause_2_graph_equation_2 {
      uint64_t x;
      List<uint64_t> xs;
      std::shared_ptr<zeros_graph> hind;
    };

    using variant_t = std::variant<Zeros_clause_2_graph_equation_1,
                                   Zeros_clause_2_graph_equation_2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    zeros_clause_2_graph() {}

    explicit zeros_clause_2_graph(Zeros_clause_2_graph_equation_1 _v)
        : v_(std::move(_v)) {}

    explicit zeros_clause_2_graph(Zeros_clause_2_graph_equation_2 _v)
        : v_(std::move(_v)) {}

    static zeros_clause_2_graph
    zeros_clause_2_graph_equation_1(uint64_t x, List<uint64_t> xs,
                                    zeros_graph hind) {
      return zeros_clause_2_graph(Zeros_clause_2_graph_equation_1{
          x, std::move(xs), std::make_shared<zeros_graph>(std::move(hind))});
    }

    static zeros_clause_2_graph
    zeros_clause_2_graph_equation_2(uint64_t x, List<uint64_t> xs,
                                    zeros_graph hind) {
      return zeros_clause_2_graph(Zeros_clause_2_graph_equation_2{
          x, std::move(xs), std::make_shared<zeros_graph>(std::move(hind))});
    }

    // MANIPULATORS
    ~zeros_clause_2_graph() {
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Zeros_clause_2_graph_equation_1>(&_v)) {
          if (_alt->hind && _alt->hind.use_count() == 1) {
            _stack.push_back(std::move(_alt->hind));
          }
        }
        if (auto *_alt = std::get_if<Zeros_clause_2_graph_equation_2>(&_v)) {
          if (_alt->hind && _alt->hind.use_count() == 1) {
            _stack.push_back(std::move(_alt->hind));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp =
                crane::any_cast<std::shared_ptr<zeros_clause_2_graph>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp =
                  crane::any_cast<std::shared_ptr<zeros_graph>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<
                      typename zeros_graph::Zeros_graph_refinement_2>(&_pv)) {
                if (_alt->hind && _alt->hind.use_count() == 1) {
                  _stack.push_back(std::move(_alt->hind));
                }
              }
            }
          }
        }
      }
    }

    zeros_clause_2_graph(const zeros_clause_2_graph &) = default;
    zeros_clause_2_graph &operator=(const zeros_clause_2_graph &) = default;
    zeros_clause_2_graph(zeros_clause_2_graph &&) = default;
    zeros_clause_2_graph &operator=(zeros_clause_2_graph &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T1
  zeros_graph_mut(T1 f, F1 &&f0,
                  std::type_identity_t<
                      crane::fn<T2(uint64_t, List<uint64_t>, zeros_graph, T1)>>
                      f1,
                  std::type_identity_t<
                      crane::fn<T2(uint64_t, List<uint64_t>, zeros_graph, T1)>>
                      f2,
                  const List<uint64_t> &x0_, uint64_t x1_,
                  const zeros_graph &x2_) {
    auto f3_impl = [&](auto &_self_f3, auto &_self_f4, const List<uint64_t> &,
                       uint64_t, const zeros_graph &z) -> T1 {
      if (std::holds_alternative<typename zeros_graph::Zeros_graph_equation_1>(
              z.v())) {
        return f;
      } else {
        const auto &[x0, xs0, hind0] =
            std::get<typename zeros_graph::Zeros_graph_refinement_2>(z.v());
        return f0(x0, xs0, *hind0,
                  _self_f4(_self_f3, _self_f4, x0, x0 == UINT64_C(0), xs0,
                           zeros_unfold_clause_2(x0, x0 == UINT64_C(0), xs0),
                           *hind0));
      }
    };
    auto f4_impl = [&](auto &_self_f3, auto &_self_f4, uint64_t, bool,
                       const List<uint64_t> &, uint64_t,
                       const zeros_clause_2_graph &z) -> T2 {
      if (std::holds_alternative<
              typename zeros_clause_2_graph::Zeros_clause_2_graph_equation_1>(
              z.v())) {
        const auto &[x0, xs0, hind0] = std::get<
            typename zeros_clause_2_graph::Zeros_clause_2_graph_equation_1>(
            z.v());
        return f1(x0, xs0, *hind0,
                  _self_f3(_self_f3, _self_f4, xs0, zeros(xs0), *hind0));
      } else {
        const auto &[x0, xs0, hind0] = std::get<
            typename zeros_clause_2_graph::Zeros_clause_2_graph_equation_2>(
            z.v());
        return f2(x0, xs0, *hind0,
                  _self_f3(_self_f3, _self_f4, xs0, zeros(xs0), *hind0));
      }
    };
    auto f3 = [&](const List<uint64_t> &_x, uint64_t _x0,
                  const zeros_graph &z) -> T1 {
      return f3_impl(f3_impl, f4_impl, _x, _x0, z);
    };
    auto f4 = [&](uint64_t _x, bool _x0, const List<uint64_t> &_x1,
                  uint64_t _x2, const zeros_clause_2_graph &z) -> T2 {
      return f4_impl(f3_impl, f4_impl, _x, _x0, _x1, _x2, z);
    };
    return f3(x0_, x1_, x2_);
  }

  template <typename T1, typename T2, typename F1, typename F2, typename F3>
  static T2 zeros_clause_2_graph_mut(T1 f, F1 &&f0, F2 &&f1, F3 &&f2,
                                     uint64_t x0_, bool x1_,
                                     const List<uint64_t> &x2_, uint64_t x3_,
                                     const zeros_clause_2_graph &x4_) {
    auto f3_impl = [&](auto &_self_f3, auto &_self_f4, const List<uint64_t> &,
                       uint64_t, const zeros_graph &z) -> T1 {
      if (std::holds_alternative<typename zeros_graph::Zeros_graph_equation_1>(
              z.v())) {
        return f;
      } else {
        const auto &[x0, xs0, hind0] =
            std::get<typename zeros_graph::Zeros_graph_refinement_2>(z.v());
        return f0(x0, xs0, *hind0,
                  _self_f4(_self_f3, _self_f4, x0, x0 == UINT64_C(0), xs0,
                           zeros_unfold_clause_2(x0, x0 == UINT64_C(0), xs0),
                           *hind0));
      }
    };
    auto f4_impl = [&](auto &_self_f3, auto &_self_f4, uint64_t, bool,
                       const List<uint64_t> &, uint64_t,
                       const zeros_clause_2_graph &z) -> T2 {
      if (std::holds_alternative<
              typename zeros_clause_2_graph::Zeros_clause_2_graph_equation_1>(
              z.v())) {
        const auto &[x0, xs0, hind0] = std::get<
            typename zeros_clause_2_graph::Zeros_clause_2_graph_equation_1>(
            z.v());
        return f1(x0, xs0, *hind0,
                  _self_f3(_self_f3, _self_f4, xs0, zeros(xs0), *hind0));
      } else {
        const auto &[x0, xs0, hind0] = std::get<
            typename zeros_clause_2_graph::Zeros_clause_2_graph_equation_2>(
            z.v());
        return f2(x0, xs0, *hind0,
                  _self_f3(_self_f3, _self_f4, xs0, zeros(xs0), *hind0));
      }
    };
    auto f3 = [&](const List<uint64_t> &_x, uint64_t _x0,
                  const zeros_graph &z) -> T1 {
      return f3_impl(f3_impl, f4_impl, _x, _x0, z);
    };
    {
      uint64_t _lc1_x = x0_;
      bool _lc1_x0 = x1_;
      const List<uint64_t> &_lc1_x1 = x2_;
      uint64_t _lc1_x2 = x3_;
      const zeros_clause_2_graph &_lc1_z = x4_;
      return f4_impl(f3_impl, f4_impl, _lc1_x, _lc1_x0, _lc1_x1, _lc1_x2,
                     _lc1_z);
    }
  }

  template <typename T1, typename T2, typename F1, typename F2, typename F3>
  static T1 zeros_graph_rect(T1 x0_, F1 &&x1_, F2 &&x2_, F3 &&x3_,
                             const List<uint64_t> &x4_, uint64_t x5_,
                             const zeros_graph &x6_) {
    return zeros_graph_mut<T1, T2>(std::move(x0_), x1_, x2_, x3_, x4_, x5_,
                                   x6_);
  }

  static zeros_graph zeros_graph_correct(const List<uint64_t> &x);

  template <typename T1>
  static T1 zeros_elim(
      T1 f,
      std::type_identity_t<crane::fn<T1(uint64_t, List<uint64_t>, T1)>> f1,
      std::type_identity_t<crane::fn<T1(uint64_t, List<uint64_t>, T1)>> f2,
      const List<uint64_t> &l) {
    return zeros_graph_mut<T1, T1>(
        std::move(f),
        [](uint64_t, List<uint64_t>, zeros_clause_2_graph, const T1 &x) {
          return x;
        },
        [=, f1 = std::move(f1)](uint64_t x, const List<uint64_t> &xs,
                                zeros_graph, const T1 &eta0_) {
          return [=](T1 _pa0) { return f1(x, xs, _pa0); }(eta0_);
        },
        [=, f2 = std::move(f2)](uint64_t x, const List<uint64_t> &xs,
                                zeros_graph, const T1 &eta0_) {
          return [=](T1 _pa0) { return f2(x, xs, _pa0); }(eta0_);
        },
        l, zeros(l), zeros_graph_correct(l));
  }

  template <typename F1, typename F2>
  static crane::obj FunctionalElimination_zeros(crane::obj x0_, F1 &&x1_,
                                                F2 &&x2_,
                                                const List<uint64_t> &x3_) {
    return zeros_elim(x0_, x1_, x2_, x3_);
  }

  struct FunctionalInduction_zeros {
    using fun_ind_prf_ty = crane::fn<zeros_graph(List<uint64_t>)>;

    static crane::fn<zeros_graph(List<uint64_t>)> fun_ind_prf() {
      return zeros_graph_correct;
    }
  };

  static_assert(FunctionalInduction<FunctionalInduction_zeros,
                                    crane::fn<uint64_t(List<uint64_t>)>>);

  template <typename F1>
  static uint64_t plain_functional(const List<uint64_t> &l, F1 &&plain0) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      return (a0 + plain0(*a1));
    }
  }

  static uint64_t plain(const List<uint64_t> &x);
  static uint64_t plain_unfold(const List<uint64_t> &l);

  struct plain_graph {
    // TYPES
    struct Plain_graph_equation_1 {};

    struct Plain_graph_equation_2 {
      uint64_t x;
      List<uint64_t> xs;
      std::shared_ptr<plain_graph> hind;
    };

    using variant_t =
        std::variant<Plain_graph_equation_1, Plain_graph_equation_2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    plain_graph() {}

    explicit plain_graph(Plain_graph_equation_1 _v) : v_(_v) {}

    explicit plain_graph(Plain_graph_equation_2 _v) : v_(std::move(_v)) {}

    static plain_graph plain_graph_equation_1() {
      return plain_graph(Plain_graph_equation_1{});
    }

    static plain_graph plain_graph_equation_2(uint64_t x, List<uint64_t> xs,
                                              plain_graph hind) {
      return plain_graph(Plain_graph_equation_2{
          x, std::move(xs), std::make_shared<plain_graph>(std::move(hind))});
    }

    // MANIPULATORS
    ~plain_graph() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<plain_graph> {
        if (auto *_alt = std::get_if<Plain_graph_equation_2>(&_v)) {
          if (_alt->hind && _alt->hind.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->hind);
          }
        }
        return nullptr;
      };
      std::shared_ptr<plain_graph> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    plain_graph(const plain_graph &) = default;
    plain_graph &operator=(const plain_graph &) = default;
    plain_graph(plain_graph &&) = default;
    plain_graph &operator=(plain_graph &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 plain_graph_rect(
      T1 f, F1 &&f0, const List<uint64_t> &_x, uint64_t _x0,
      const plain_graph &p) { /// CraneEnter: captures varying parameters for
                              /// each recursive call.

    struct CraneEnter {
      const plain_graph *p;
      uint64_t _x0;
      List<uint64_t> _x;
    };

    /// CraneCont_Plain_graph_equation_2: saves [x0, xs0, hind0], resumes after
    /// recursive call, then processes rest.
    struct CraneCont_Plain_graph_equation_2 {
      uint64_t x0;
      List<uint64_t> xs0;
      std::shared_ptr<plain_graph> hind0;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_Plain_graph_equation_2>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&p, _x0, _x});
    /// Loopified plain_graph_rect: CraneEnter ->
    /// CraneCont_Plain_graph_equation_2.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const plain_graph &p = *_f.p;
        uint64_t _x0 = _f._x0;
        const List<uint64_t> &_x = std::move(_f._x);
        if (std::holds_alternative<
                typename plain_graph::Plain_graph_equation_1>(p.v())) {
          _result = f;
        } else {
          const auto &[x0, xs0, hind0] =
              std::get<typename plain_graph::Plain_graph_equation_2>(p.v());
          _stack.emplace_back(CraneCont_Plain_graph_equation_2{x0, xs0, hind0});
          _stack.emplace_back(CraneEnter{crane_raw(hind0), plain(xs0), xs0});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Plain_graph_equation_2>(_frame));
        uint64_t x0 = _f.x0;
        List<uint64_t> xs0 = std::move(_f.xs0);
        std::shared_ptr<plain_graph> hind0 = std::move(_f.hind0);
        _result = f0(x0, xs0, *hind0, std::move(_result));
      }
    }
    return _result;
  }

  static plain_graph plain_graph_correct(const List<uint64_t> &x);

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, List<uint64_t> &,
                                   T1 &&>
  static T1 plain_elim(T1 f, F1 &&f0, const List<uint64_t> &l) {
    {
      const List<uint64_t> &_lc1_x = l;
      uint64_t _lc1_x0 = plain(l);
      const plain_graph &_lc1_p = plain_graph_correct(l);

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const plain_graph *p;
        uint64_t _x0;
        List<uint64_t> _x;
      };

      /// CraneCont_Plain_graph_equation_2: saves [x0, xs0], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_Plain_graph_equation_2 {
        uint64_t x0;
        List<uint64_t> xs0;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Plain_graph_equation_2>;
      T1 _lc1_result{};
      crane::small_vector<CraneFrame> _lc1_stack;
      _lc1_stack.emplace_back(CraneEnter{&_lc1_p, _lc1_x0, _lc1_x});
      /// Loopified f1: CraneEnter -> CraneCont_Plain_graph_equation_2.
      while (!_lc1_stack.empty()) {
        CraneFrame _frame = std::move(_lc1_stack.back());
        _lc1_stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const plain_graph &_lc1_p = *_f.p;
          uint64_t _lc1_x0 = _f._x0;
          const List<uint64_t> &_lc1_x = std::move(_f._x);
          if (std::holds_alternative<
                  typename plain_graph::Plain_graph_equation_1>(_lc1_p.v())) {
            _lc1_result = f;
          } else {
            const auto &[x0, xs0, hind0] =
                std::get<typename plain_graph::Plain_graph_equation_2>(
                    _lc1_p.v());
            _lc1_stack.emplace_back(CraneCont_Plain_graph_equation_2{x0, xs0});
            _lc1_stack.emplace_back(
                CraneEnter{crane_raw(hind0), plain(xs0), xs0});
          }
        } else {
          auto _f =
              std::move(std::get<CraneCont_Plain_graph_equation_2>(_frame));
          uint64_t x0 = _f.x0;
          List<uint64_t> xs0 = std::move(_f.xs0);
          _lc1_result = f0(x0, xs0, std::move(_lc1_result));
        }
      }
      return _lc1_result;
    }
  }

  template <typename F1>
  static crane::obj FunctionalElimination_plain(crane::obj x0_, F1 &&x1_,
                                                const List<uint64_t> &x2_) {
    return plain_elim(x0_, x1_, x2_);
  }

  struct FunctionalInduction_plain {
    using fun_ind_prf_ty = crane::fn<plain_graph(List<uint64_t>)>;

    static crane::fn<plain_graph(List<uint64_t>)> fun_ind_prf() {
      return plain_graph_correct;
    }
  };

  static_assert(FunctionalInduction<FunctionalInduction_plain,
                                    crane::fn<uint64_t(List<uint64_t>)>>);
};

#endif // INCLUDED_LOOPIFY_EQUATIONS_WITH_CLAUSE
