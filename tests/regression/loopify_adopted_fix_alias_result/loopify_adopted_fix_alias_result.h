#ifndef INCLUDED_LOOPIFY_ADOPTED_FIX_ALIAS_RESULT
#define INCLUDED_LOOPIFY_ADOPTED_FIX_ALIAS_RESULT

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }
};

/// A machine adopting a local fixpoint that calls back into its function,
/// the function's result written through a type abbreviation -- the shape
/// of FMapList.map2 and combine.
///
/// The function returns t C; extraction gives the fixpoint the unfolded
/// list (nat * C), and the C++ spells the two t<T3> and
/// List<std::pair<uint64_t, T3>>.  The frame transform once told
/// them apart by that spelling, dropped the adoption the plan had made,
/// and left map2 the recursion it is.
struct LoopifyAdoptedFixAliasResult {
  template <typename a> using t = List<std::pair<uint64_t, a>>;

  template <typename T1>
  static t<T1> option_cons(uint64_t k, const std::optional<T1> &o,
                           List<std::pair<uint64_t, T1>> l) {
    if (o.has_value()) {
      const T1 &e = *o;
      return List<std::pair<uint64_t, T1>>::cons(std::make_pair(k, e),
                                                 std::move(l));
    } else {
      return l;
    }
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static t<T3> map2_l(F0 &&f, const List<std::pair<uint64_t, T1>>
                                  &m) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

    struct CraneEnter {
      const List<std::pair<uint64_t, T1>> *m;
    };

    /// CraneCont_k: saves [k, e], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_k {
      uint64_t k;
      T1 e;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_k>;
    t<T3> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&m});
    /// Loopified map2_l: CraneEnter -> CraneCont_k.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<std::pair<uint64_t, T1>> &m = *_f.m;
        if (std::holds_alternative<typename List<std::pair<uint64_t, T1>>::Nil>(
                m.v())) {
          _result = List<std::pair<uint64_t, T3>>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<std::pair<uint64_t, T1>>::Cons>(m.v());
          const auto &[k, e] = a0;
          _stack.emplace_back(CraneCont_k{k, e});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_k>(_frame));
        uint64_t k = _f.k;
        auto e = std::move(_f.e);
        _result = option_cons<T3>(
            k, f(std::make_optional<T1>(e), std::optional<T2>()),
            std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static t<T3> map2_r(F0 &&f, const List<std::pair<uint64_t, T2>>
                                  &m) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

    struct CraneEnter {
      const List<std::pair<uint64_t, T2>> *m;
    };

    /// CraneCont_k: saves [k, e], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_k {
      uint64_t k;
      T2 e;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_k>;
    t<T3> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&m});
    /// Loopified map2_r: CraneEnter -> CraneCont_k.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<std::pair<uint64_t, T2>> &m = *_f.m;
        if (std::holds_alternative<typename List<std::pair<uint64_t, T2>>::Nil>(
                m.v())) {
          _result = List<std::pair<uint64_t, T3>>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<std::pair<uint64_t, T2>>::Cons>(m.v());
          const auto &[k, e] = a0;
          _stack.emplace_back(CraneCont_k{k, e});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_k>(_frame));
        uint64_t k = _f.k;
        auto e = std::move(_f.e);
        _result = option_cons<T3>(
            k, f(std::optional<T1>(), std::make_optional<T2>(e)),
            std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static t<T3> map2(F0 &&f, List<std::pair<uint64_t, T1>> m,
                    t<T2> x0_) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

    struct CraneEnter {
      t<T2> x0_;
      List<std::pair<uint64_t, T1>> m;
    };

    /// CraneEnter_map2_aux: captures varying parameters for each recursive
    /// call.
    struct CraneEnter_map2_aux {
      List<std::pair<uint64_t, T2>> m_;
      std::shared_ptr<List<std::pair<uint64_t, T1>>> a1;
      T1 e;
      std::decay_t<F0> f;
      uint64_t k;
      List<std::pair<uint64_t, T1>> m;
    };

    /// CraneCont1: saves [f, k, e], resumes after recursive call, then
    /// processes rest.
    struct CraneCont1 {
      std::decay_t<F0> f;
      uint64_t k;
      T1 e;
    };

    /// CraneCont2: saves [f, k_, e_], resumes after recursive call, then
    /// processes rest.
    struct CraneCont2 {
      std::decay_t<F0> f;
      uint64_t k_;
      T2 e_;
    };

    /// CraneCont3: saves [f, k, e, e_], resumes after recursive call, then
    /// processes rest.
    struct CraneCont3 {
      std::decay_t<F0> f;
      uint64_t k;
      T1 e;
      T2 e_;
    };

    using CraneFrame = std::variant<CraneEnter, CraneEnter_map2_aux, CraneCont1,
                                    CraneCont2, CraneCont3>;
    t<T3> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{std::move(x0_), std::move(m)});
    /// Loopified map2: CraneEnter -> CraneCont1 -> CraneCont2 -> CraneCont3.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        t<T2> x0_ = std::move(_f.x0_);
        List<std::pair<uint64_t, T1>> m = std::move(_f.m);
        if (std::holds_alternative<typename List<std::pair<uint64_t, T1>>::Nil>(
                m.v_mut())) {
          _result = map2_r<T1, T2, T3>(f, std::move(x0_));
        } else {
          auto &[a0, a1] =
              std::get<typename List<std::pair<uint64_t, T1>>::Cons>(m.v_mut());
          const auto &[k, e] = a0;
          {
          }
          {
          }
          _stack.emplace_back(
              CraneEnter_map2_aux{std::move(x0_), a1, e, f, k, m});
        }
      } else if (std::holds_alternative<CraneEnter_map2_aux>(_frame)) {
        auto _f = std::move(std::get<CraneEnter_map2_aux>(_frame));
        const List<std::pair<uint64_t, T2>> &m_ = std::move(_f.m_);
        std::shared_ptr<List<std::pair<uint64_t, T1>>> a1 = std::move(_f.a1);
        auto e = std::move(_f.e);
        auto f = std::move(_f.f);
        uint64_t k = _f.k;
        List<std::pair<uint64_t, T1>> m = std::move(_f.m);
        if (std::holds_alternative<typename List<std::pair<uint64_t, T2>>::Nil>(
                m_.v())) {
          _result = map2_l<T1, T2, T3>(f, m);
        } else {
          const auto &[a00, a10] =
              std::get<typename List<std::pair<uint64_t, T2>>::Cons>(m_.v());
          const auto &[k_, e_] = a00;
          if (k < k_) {
            _stack.emplace_back(CraneCont1{f, k, std::move(e)});
            _stack.emplace_back(CraneEnter{m_, *a1});
          } else {
            if (k_ < k) {
              _stack.emplace_back(CraneCont2{f, k_, e_});
              _stack.emplace_back(CraneEnter_map2_aux{*a10, a1, e, f, k, m});
            } else {
              _stack.emplace_back(CraneCont3{f, k, std::move(e), e_});
              _stack.emplace_back(CraneEnter{*a10, *a1});
            }
          }
        }
      } else if (std::holds_alternative<CraneCont1>(_frame)) {
        auto _f = std::move(std::get<CraneCont1>(_frame));
        std::decay_t<F0> f = std::move(_f.f);
        uint64_t k = _f.k;
        auto e = std::move(_f.e);
        _result = option_cons<T3>(
            k, f(std::make_optional<T1>(e), std::optional<T2>()),
            std::move(_result));
      } else if (std::holds_alternative<CraneCont2>(_frame)) {
        auto _f = std::move(std::get<CraneCont2>(_frame));
        std::decay_t<F0> f = std::move(_f.f);
        uint64_t k_ = _f.k_;
        auto e_ = std::move(_f.e_);
        _result = option_cons<T3>(
            k_, f(std::optional<T1>(), std::make_optional<T2>(e_)),
            std::move(_result));
      } else {
        auto _f = std::move(std::get<CraneCont3>(_frame));
        std::decay_t<F0> f = std::move(_f.f);
        uint64_t k = _f.k;
        auto e = std::move(_f.e);
        auto e_ = std::move(_f.e_);
        _result = option_cons<T3>(
            k, f(std::make_optional<T1>(e), std::make_optional<T2>(e_)),
            std::move(_result));
      }
    }
    return _result;
  }

  static std::optional<uint64_t> add_opt(const std::optional<uint64_t> &a,
                                         const std::optional<uint64_t> &b);
  static uint64_t sum(const List<std::pair<uint64_t, uint64_t>> &m);
  /// The keys i * step, ..., (i + n - 1) * step, each bound to its
  /// multiple.
  static t<uint64_t> keys(uint64_t n, uint64_t i, uint64_t step);
  static t<uint64_t> merged(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_ADOPTED_FIX_ALIAS_RESULT
