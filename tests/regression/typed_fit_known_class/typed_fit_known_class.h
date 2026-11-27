#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include "shared_block.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename E, typename R, typename itree> struct ItreeF;
template <typename E, typename R> struct Itree;

struct Function {
  static crane::obj Id_IFun(crane::obj e);
};

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

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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

template <typename obj, typename c> using Id_ = crane::fn<c(obj)>;
template <typename obj, typename c> using ReSum = c;

struct CategoryOps {
  template <typename T1, typename T2>
  static T2 id_(const std::type_identity_t<Id_<T1, T2>> &id_0, const T1 &x0_);
  template <typename T1, typename T2>
  static T2 resum(const T1 &_x, const T1 &_x0, T2 reSum);
  template <typename T1, typename T2>
  static ReSum<T1, T2> ReSum_id(const std::type_identity_t<Id_<T1, T2>> &x0_,
                                const T1 &x1_);
};

template <typename E, typename R, typename itree> struct ItreeF {
  // TYPES
  struct RetF {
    R r;
  };

  struct TauF {
    itree t;
  };

  struct VisF {
    E x;
    crane::fn<itree(crane::obj)> e;
  };

  using variant_t = std::variant<RetF, TauF, VisF>;
  using crane_family_tag = void;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  ItreeF() {}

  explicit ItreeF(RetF _v) : v_(std::move(_v)) {}

  explicit ItreeF(TauF _v) : v_(std::move(_v)) {}

  explicit ItreeF(VisF _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1, typename CraneU2>
  ItreeF(const ItreeF<CraneU0, CraneU1, CraneU2> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<
                  typename ItreeF<CraneU0, CraneU1, CraneU2>::RetF>(_other.v())) {
            const auto &[r] =
                std::get<typename ItreeF<CraneU0, CraneU1, CraneU2>::RetF>(
                    _other.v());
            return RetF{[&]() -> R {
              if constexpr (crane_convertible<R, const CraneU1 &>) {
                return crane_convert<R>(r);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else if (
              std::holds_alternative<
                  typename ItreeF<CraneU0, CraneU1, CraneU2>::TauF>(_other.v())) {
            const auto &[t] =
                std::get<typename ItreeF<CraneU0, CraneU1, CraneU2>::TauF>(
                    _other.v());
            return TauF{[&]() -> itree {
              if constexpr (crane_convertible<itree, const CraneU2 &>) {
                return crane_convert<itree>(t);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[x, e] =
                std::get<typename ItreeF<CraneU0, CraneU1, CraneU2>::VisF>(
                    _other.v());
            return VisF{
                [&]() -> E {
                  if constexpr (crane_convertible<E, const CraneU0 &>) {
                    return crane_convert<E>(x);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                crane_convert<crane::fn<itree(crane::obj)>>(e)};
          }
        }()) {}

  static ItreeF<E, R, itree> retf(R r) {
    return ItreeF<E, R, itree>(RetF{std::move(r)});
  }

  static ItreeF<E, R, itree> tauf(itree t) {
    return ItreeF<E, R, itree>(TauF{std::move(t)});
  }

  static ItreeF<E, R, itree> visf(E x, crane::fn<itree(crane::obj)> e) {
    return ItreeF<E, R, itree>(VisF{std::move(x), std::move(e)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename E, typename R> struct Itree {
  // TYPES
  template <typename CraneS0 = Itree<E, R>> struct Go_ {
    ItreeF<E, R, CraneS0> _observe;
  };

  using Go = Go_<>;
  using variant_t = std::variant<Go>;
  using crane_family_tag = void;

private:
  // DATA
  crane::lazy<variant_t> lazy_v_;

public:
  // CREATORS
  Itree() {}

  explicit Itree(Go _v)
      : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  template <typename CraneU0, typename CraneU1>
  Itree(const Itree<CraneU0, CraneU1> &_other)
      : lazy_v_(crane::lazy<variant_t>::converted_from(
      _other.lazy_cell(), [=]() -> variant_t {
        const auto &[_observe] =
            std::get<typename Itree<CraneU0, CraneU1>::Go>(_other.v());
        return Go{crane_convert<ItreeF<E, R, Itree<E, R>>>(_observe)};
      })) {}

  explicit Itree(crane::fn<variant_t()> _thunk)
      : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  static Itree<E, R> go(ItreeF<E, R, Itree<E, R>> _observe) {
    return Itree<E, R>(crane::lazy<variant_t>(
        std::in_place, std::in_place_index<0>, std::move(_observe)));
  }

  explicit Itree(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

  template <typename F> static Itree<E, R> lazy_(F &&thunk) {
    return Itree<E, R>(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
  }

  // ACCESSORS
  const variant_t &v() const { return lazy_v_.force(); }

  const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }

  const ItreeF<E, R, Itree<E, R>> &observe() const & {
    const auto &[_observe] = std::get<typename Itree<E, R>::Go>(this->v());
    return _observe;
  }

  ItreeF<E, R, Itree<E, R>> observe() const && {
    const auto &[_observe] = std::get<typename Itree<E, R>::Go>(this->v());
    return _observe;
  }
};

struct ITree {
  template <typename T1, typename T2, typename T3>
  static Itree<T1, T3>
  subst(std::type_identity_t<crane::fn<Itree<T1, T3>(T2)>> k,
        const Itree<T1, T2> &u) {
    auto &&_sv = u.observe();
    if (std::holds_alternative<typename ItreeF<T1, T2, Itree<T1, T2>>::RetF>(
            _sv.v())) {
      const auto &[r0] =
          std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::RetF>(_sv.v());
      return k(r0);
    } else if (
        std::holds_alternative<typename ItreeF<T1, T2, Itree<T1, T2>>::TauF>(
            _sv.v())) {
      const auto &[t0] =
          std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::TauF>(_sv.v());
      return Itree<T1, T3>::lazy_(
          [=, k = std::move(k)]() mutable -> typename Itree<T1,
                                                            T3>::Go {
            return {ItreeF<T1, T3, Itree<T1, T3>>::tauf(
                subst<T1, T2, T3>(std::move(k), t0))};
          });
    } else {
      const auto &[x, e0] =
          std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::VisF>(_sv.v());
      return Itree<T1, T3>::go(ItreeF<T1, T3, Itree<T1, T3>>::visf(
          x,
          crane::fn<Itree<T1, T3>(crane::obj)>([=, e0 = e0, k = std::move(k)](
              const crane::obj &x0)
                                                    -> Itree<T1,
                                                             T3> {
            return subst<T1, T2, T3>(k, crane_call_erased(e0, x0));
          })));
    }
  }

  template <typename T1, typename T2, typename T3>
  static Itree<T1, T3>
  bind(const Itree<T1, T2> &u,
       std::type_identity_t<crane::fn<Itree<T1, T3>(T2)>> k) {
    return subst<T1, T2, T3>(std::move(k), u);
  }

  template <typename T1, typename T2>
  static Itree<T1, T2> trigger(crane::rebind_t<T1, T2> e) {
    return Itree<T1, T2>::go(ItreeF<T1, T2, Itree<T1, T2>>::visf(
        std::move(e),
        crane::fn<Itree<T1, T2>(crane::obj)>(
            [](const crane::obj &x) -> Itree<T1,
                                             T2> {
              return Itree<T1, T2>::go(
                  ItreeF<T1, T2, Itree<T1, T2>>::retf(crane_any_cast<T2>(x)));
            })));
  }
};

template <typename e, typename f> using IFun = crane::fn<f(e)>;

struct Subevent {
  template <typename T1, typename T2, typename T3>
  static crane::rebind_t<T2, T3>
  subevent(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h,
           crane::rebind_t<T1, T3> x);
};

template <typename I>
concept Measured = requires {
  typename I::template F<crane::obj>;
  {
    I::template measure<crane::obj>(
        std::declval<typename I::template F<crane::obj>>())
  } -> std::convertible_to<uint64_t>;
};

struct TypedFitKnownClass {
  enum class AskE { ASK };
  static inline const Itree<AskE, uint64_t> program = []() {
    return ITree::template bind<AskE, uint64_t, uint64_t>(
        ITree::template trigger<AskE, uint64_t>(Subevent::template subevent<
            AskE, AskE, uint64_t>(
            CategoryOps::template ReSum_id<crane::obj,
                                           crane::fn<crane::obj(crane::obj)>>(
                [](crane::obj) {
                  return crane_erase_global<Function::Id_IFun, crane::obj>();
                },
                crane::obj()),
            AskE::ASK)),
        [](uint64_t x) {
          // Built on the first call and immortal: every thread reads it without
          // touching its counts.
          static const auto resum_id =
              crane::immortal(CategoryOps::template ReSum_id<
                  crane::obj, crane::fn<crane::obj(crane::obj)>>(
                  [](crane::obj) {
                    return crane_erase_global<Function::Id_IFun, crane::obj>();
                  },
                  crane::obj()));
          return ITree::template bind<AskE, uint64_t, uint64_t>(
              ITree::template trigger<AskE, uint64_t>(
                  Subevent::template subevent<AskE, AskE, uint64_t>(resum_id,
                                                                    AskE::ASK)),
              [=](uint64_t y) {
                return Itree<AskE, uint64_t>::go(
                    ItreeF<AskE, uint64_t, Itree<AskE, uint64_t>>::retf(x + y));
              });
        });
  }();
  static std::optional<uint64_t> answer(uint64_t fuel,
                                        const Itree<AskE, uint64_t> &t);
  static inline const bool answered = []() -> bool {
    auto _cs = answer(UINT64_C(100), program);
    if (_cs.has_value()) {
      const uint64_t &n = *_cs;
      return n == UINT64_C(6);
    } else {
      return false;
    }
  }();

  template <Measured _tcI0, typename T2>
  static uint64_t measure(typename _tcI0::template F<T2> x) {
    return _tcI0::template measure<T2>(std::move(x));
  }

  template <typename T1> static uint64_t count(const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[_, a1] = std::get<typename List<T1>::Cons>(l.v());
      return (count<T1>(*a1) + 1);
    }
  }

  struct ML {
    template <typename CraneA0> using F = List<CraneA0>;

    template <typename CraneA0> static uint64_t measure(List<CraneA0> a0) {
      return count<CraneA0>(std::move(a0));
    }
  };

  static_assert(Measured<ML>);
  static uint64_t measure_list(const List<uint64_t> &l);
  static inline const uint64_t measure_three =
      measure_list(List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))));
};

template <typename T1, typename T2>
T2 CategoryOps::id_(const std::type_identity_t<Id_<T1, T2>> &id_0,
                    const T1 &x0_) {
  return id_0(x0_);
}

template <typename T1, typename T2>
T2 CategoryOps::resum(const T1 &, const T1 &, T2 reSum) {
  return reSum;
}

template <typename T1, typename T2>
ReSum<T1, T2>
CategoryOps::ReSum_id(const std::type_identity_t<Id_<T1, T2>> &x0_,
                      const T1 &x1_) {
  return CategoryOps::template id_<T1, T2>(x0_, x1_);
}

template <typename T1, typename T2, typename T3>
crane::rebind_t<T2, T3>
Subevent::subevent(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h,
                   crane::rebind_t<T1, T3> x) {
  return crane_any_cast<crane::rebind_t<T2, T3>>(CategoryOps::resum(
      crane::obj(), crane::obj(), std::move(h))(std::move(x)));
}
