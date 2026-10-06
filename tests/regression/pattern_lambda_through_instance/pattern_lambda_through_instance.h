#ifndef INCLUDED_PATTERN_LAMBDA_THROUGH_INSTANCE
#define INCLUDED_PATTERN_LAMBDA_THROUGH_INSTANCE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

template <typename I, typename T>
concept Endo = requires {
  { I::endo(std::declval<T>()) } -> std::convertible_to<T>;
};
template <typename I>
concept TFunctor = requires {
  typename I::template T<crane::obj>;
  {
    I::template tfmap<crane::obj, crane::obj>(
        std::declval<crane::fn<crane::obj(crane::obj)>>(),
        std::declval<typename I::template T<crane::obj>>())
  } -> std::convertible_to<typename I::template T<crane::obj>>;
};

struct PatternLambdaThroughInstance {
  template <typename _tcI0, typename T1>
    requires Endo<_tcI0, T1>
  static T1 endo(T1 x0_) {
    return _tcI0::endo(std::move(x0_));
  }

  template <TFunctor _tcI0, typename T2, typename T3, typename F0>
  static typename _tcI0::template T<T3>
  tfmap(F0 &&f, typename _tcI0::template T<T2> x) {
    return _tcI0::template tfmap<T2, T3>(f, std::move(x));
  }

  struct TFunctor_list {
    template <typename CraneA0> using T = List<CraneA0>;

    template <typename CraneA0, typename CraneA1>
    static List<CraneA1> tfmap(crane::fn<CraneA1(CraneA0)> a0,
                               List<CraneA0> a1) {
      return a1.template map<CraneA1>(std::move(a0));
    }
  };

  static_assert(TFunctor<TFunctor_list>);

  template <typename T> struct exp {
    // DATA
    T a0;

    // ACCESSORS
    exp<T> clone() const { return {a0}; }

    template <typename CraneU> operator exp<CraneU>() const {
      return {[&]() -> CraneU {
        if constexpr (crane_convertible<CraneU, const T &>) {
          return crane_convert<CraneU>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }

    // CREATORS
    static exp<T> lit(T a0) { return {std::move(a0)}; }

    template <typename T1, typename F0> T1 exp_rec(F0 &&f) const {
      return this->template exp_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const T &>
    T1 exp_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }
  };

  struct TFunctor_exp {
    template <typename CraneA0> using T = exp<CraneA0>;

    template <typename CraneA0, typename CraneA1>
    static exp<CraneA1> tfmap(crane::fn<CraneA1(CraneA0)> f, exp<CraneA0> e) {
      const auto &[a0] = e;
      return exp<CraneA1>::lit(f(a0));
    }
  };

  static_assert(TFunctor<TFunctor_exp>);

  template <typename T> struct phi {
    // DATA
    T a0;
    List<std::pair<uint64_t, exp<T>>> a1;

    // ACCESSORS
    phi<T> clone() const { return {a0, a1}; }

    template <typename CraneU> operator phi<CraneU>() const {
      return {[&]() -> CraneU {
                if constexpr (crane_convertible<CraneU, const T &>) {
                  return crane_convert<CraneU>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }(),
              crane_convert<List<std::pair<uint64_t, exp<CraneU>>>>(a1)};
    }

    // CREATORS
    static phi<T> phi0(T a0, List<std::pair<uint64_t, exp<T>>> a1) {
      return {std::move(a0), std::move(a1)};
    }
  };

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const T1 &,
                                   const List<std::pair<uint64_t, exp<T1>>> &>
  static T2 phi_rect(F0 &&f, const phi<T1> &p) {
    const auto &[a0, a1] = p;
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename F0>
  static T2 phi_rec(F0 &&f, const phi<T1> &p) {
    return phi_rect<T1, T2>(f, p);
  }

  template <typename _tcI0, TFunctor _tcI1>
    requires Endo<_tcI0, uint64_t>
  struct TFunctor_phi {
    template <typename CraneA0> using T = phi<CraneA0>;

    template <typename CraneA0, typename CraneA1>
    static phi<CraneA1> tfmap(crane::fn<CraneA1(CraneA0)> f, phi<CraneA0> pat) {
      const auto &[a0, a1] = pat;
      return phi<CraneA1>::phi0(
          f(a0),
          TFunctor_list::template tfmap<std::pair<uint64_t, exp<CraneA0>>,
                                        std::pair<uint64_t, exp<CraneA1>>>(
              [=](const std::pair<uint64_t, exp<CraneA0>> &pat0) {
                const auto &[id, e] = pat0;
                return std::make_pair(
                    _tcI0::endo(id),
                    _tcI1::template tfmap<CraneA0, CraneA1>(f, e));
              },
              a1));
    }
  };

  struct Endo_nat {
    constexpr static uint64_t endo(uint64_t x) { return (x + 1); }
  };

  static_assert(Endo<Endo_nat, uint64_t>);
  static inline const phi<uint64_t> p0 = phi<uint64_t>::phi0(
      UINT64_C(1),
      List<std::pair<uint64_t, exp<uint64_t>>>::cons(
          std::make_pair(UINT64_C(2), exp<uint64_t>::lit(UINT64_C(3))),
          List<std::pair<uint64_t, exp<uint64_t>>>::cons(
              std::make_pair(UINT64_C(4), exp<uint64_t>::lit(UINT64_C(5))),
              List<std::pair<uint64_t, exp<uint64_t>>>::nil())));
  static inline const phi<bool> p1 =
      TFunctor_phi<Endo_nat, TFunctor_exp>::template tfmap<uint64_t, bool>(
          [](uint64_t n) { return n == UINT64_C(3); }, p0);
  static inline const uint64_t result = []() {
    return []() {
      const auto &_sv = p1;
      const auto &[a0, a1] = _sv;
      return ((a0 ? UINT64_C(100) : UINT64_C(0)) +
              a1.template fold_left<uint64_t>(
                  [](uint64_t acc, const std::pair<uint64_t, exp<bool>> &pat) {
                    const auto &[id, e] = pat;
                    const auto &[a2] = e;
                    return ((acc + id) + (a2 ? UINT64_C(10) : UINT64_C(0)));
                  },
                  UINT64_C(0)));
    }();
  }();
};

#endif // INCLUDED_PATTERN_LAMBDA_THROUGH_INSTANCE
