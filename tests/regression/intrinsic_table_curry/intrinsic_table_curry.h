#ifndef INCLUDED_INTRINSIC_TABLE_CURRY
#define INCLUDED_INTRINSIC_TABLE_CURRY

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Empty_set;
struct Nat;
template <typename A, typename B> struct Sum;
template <typename A> struct List;
template <typename E, typename R, typename itree> struct ItreeF;
template <typename E, typename R> struct Itree;

struct Empty_set {
  Empty_set() = delete;
};

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool eqb(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return true;
        } else {
          return false;
        }
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return false;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_loop_m->v());
          _loop_self = crane_raw(a0);
          _loop_m = crane_raw(a00);
        }
      }
    }
  }

  Nat add(Nat m) const {
    std::shared_ptr<Nat> _head{};
    std::shared_ptr<Nat> *_write = &_head;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        *_write = std::make_shared<Nat>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = std::make_shared<Nat>(typename Nat::S(nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename Nat::S>((*_write)->v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_head);
  }
};

template <typename A, typename B> struct Sum {
  // TYPES
  struct Inl {
    A a0;
  };

  struct Inr {
    B a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum() {}

  explicit Sum(Inl _v) : v_(std::move(_v)) {}

  explicit Sum(Inr _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1>
  Sum(const Sum<CraneU0, CraneU1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum<CraneU0, CraneU1>::Inl>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inl>(_other.v());
            return Inl{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU0 &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inr>(_other.v());
            return Inr{[&]() -> B {
              if constexpr (crane_convertible<B, const CraneU1 &>) {
                return crane_convert<B>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Sum<A, B> inl(A a0) { return Sum<A, B>(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum<A, B>(Inr{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
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

  Nat length() const {
    std::shared_ptr<Nat> _head{};
    std::shared_ptr<Nat> *_write = &_head;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<Nat>(Nat::o());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = std::make_shared<Nat>(typename Nat::S(nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename Nat::S>((*_write)->v_mut()).a0;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
};

template <typename obj, typename c> using Id_ = crane::fn<c(obj)>;
template <typename obj, typename c> using ReSum = c;

struct CategoryOps {
  template <typename T1, typename T2>
  static T2 id_(std::type_identity_t<Id_<T1, T2>> id_0, T1 x0_);
  template <typename T1, typename T2>
  static T2 resum(const T1 &_x, const T1 &_x0, T2 reSum);
  template <typename T1, typename T2>
  static ReSum<T1, T2> ReSum_id(std::type_identity_t<Id_<T1, T2>> x0_,
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
                  typename ItreeF<CraneU0, CraneU1, CraneU2>::RetF>(
                  _other.v())) {
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
          } else {
            if (std::holds_alternative<
                    typename ItreeF<CraneU0, CraneU1, CraneU2>::TauF>(
                    _other.v())) {
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
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  crane_convert<crane::fn<itree(crane::obj)>>(e)};
            }
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
    return Itree<E, R>(
        crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
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
  subst(std::type_identity_t<crane::fn<Itree<T1, T3>(T2)>> k, Itree<T1, T2> u) {
    auto &&_sv = u.observe();
    if (std::holds_alternative<typename ItreeF<T1, T2, Itree<T1, T2>>::RetF>(
            _sv.v())) {
      const auto &[r0] =
          std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::RetF>(_sv.v());
      return k(r0);
    } else if (std::holds_alternative<
                   typename ItreeF<T1, T2, Itree<T1, T2>>::TauF>(_sv.v())) {
      const auto &[t0] =
          std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::TauF>(_sv.v());
      return Itree<T1, T3>::lazy_([=]() -> Itree<T1, T3> {
        return Itree<T1, T3>::go(
            ItreeF<T1, T3, Itree<T1, T3>>::tauf(subst<T1, T2, T3>(k, t0)));
      });
    } else {
      const auto &[x, e0] =
          std::get<typename ItreeF<T1, T2, Itree<T1, T2>>::VisF>(_sv.v());
      return Itree<T1, T3>::go(ItreeF<T1, T3, Itree<T1, T3>>::visf(
          x, crane::fn<Itree<T1, T3>(crane::obj)>(
                 [=](const crane::obj &x0) -> Itree<T1, T3> {
                   return subst<T1, T2, T3>(k, crane_call_erased(e0, x0));
                 })));
    }
  }

  template <typename T1, typename T2, typename T3>
  static Itree<T1, T3>
  bind(Itree<T1, T2> u, std::type_identity_t<crane::fn<Itree<T1, T3>(T2)>> k) {
    return subst<T1, T2, T3>(std::move(k), u);
  }

  template <typename T1, typename T2>
  static Itree<T1, T2> trigger(crane::rebind_t<T1, T2> e) {
    return Itree<T1, T2>::go(ItreeF<T1, T2, Itree<T1, T2>>::visf(
        std::move(e),
        crane::fn<Itree<T1, T2>(crane::obj)>(
            [](const crane::obj &x) -> Itree<T1, T2> {
              return Itree<T1, T2>::go(
                  ItreeF<T1, T2, Itree<T1, T2>>::retf(crane_any_cast<T2>(x)));
            })));
  }
};

template <typename e, typename f> using IFun = crane::fn<f(e)>;

struct Function {
  static crane::obj Id_IFun(crane::obj e);
};

struct Subevent {
  template <typename T1, typename T2, typename T3>
  static crane::rebind_t<T2, T3>
  subevent(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h,
           crane::rebind_t<T1, T3> x);
};

template <typename
I>concept Params = requires {
    typename I::ptr;
  } && (requires {
    { I::zero() } -> std::convertible_to<typename I::ptr>;
  } || requires {
    { I::zero } -> std::convertible_to<typename I::ptr>;
  });

struct IntrinsicTableCurry {
  using ptr = crane::obj;
  enum class FailE { FAIL };
  using pure_function = crane::fn<std::optional<Sum<Nat, Nat>>(List<Nat>)>;
  template <typename ptr, typename e>
  using semantic_function =
      crane::fn<Itree<e, Sum<Nat, Nat>>(List<Nat>, std::optional<ptr>)>;
  template <typename ptr, typename e>
  using intrinsic_definitions = List<std::pair<Nat, semantic_function<ptr, e>>>;

  template <typename T1>
  static Itree<T1, Sum<Nat, Nat>>
  to_itree(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h,
           const std::optional<Sum<Nat, Nat>> &o) {
    if (o.has_value()) {
      const Sum<Nat, Nat> &r = *o;
      return Itree<T1, Sum<Nat, Nat>>::go(
          ItreeF<T1, Sum<Nat, Nat>, Itree<T1, Sum<Nat, Nat>>>::retf(r));
    } else {
      return ITree::template bind<T1, Empty_set, Sum<Nat, Nat>>(
          ITree::template trigger<T1, Empty_set>(
              Subevent::template subevent<FailE, T1, Empty_set>(std::move(h),
                                                                FailE::FAIL)),
          [](Empty_set) -> Itree<T1, Sum<Nat, Nat>> {
            throw std::logic_error("absurd case");
          });
    }
  }

  template <Params _tcI0, typename T1>
  static semantic_function<typename _tcI0::ptr, T1>
  pure_to_semantic(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h,
                   pure_function f) {
    return [=](const List<Nat> &args, std::optional<typename _tcI0::ptr>) {
      return to_itree<T1>(h, f(args));
    };
  }

  static inline const pure_function p1 =
      [](const List<Nat> &args) -> std::optional<Sum<Nat, Nat>> {
    if (std::holds_alternative<typename List<Nat>::Nil>(args.v())) {
      return std::optional<Sum<Nat, Nat>>();
    } else {
      const auto &[a0, a1] = std::get<typename List<Nat>::Cons>(args.v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<Nat>::Nil>(_sv.v())) {
        return std::make_optional<Sum<Nat, Nat>>(
            Sum<Nat, Nat>::inl(Nat::s(a0)));
      } else {
        return std::optional<Sum<Nat, Nat>>();
      }
    }
  };
  static inline const pure_function p2 =
      [](const List<Nat> &args) -> std::optional<Sum<Nat, Nat>> {
    if (std::holds_alternative<typename List<Nat>::Nil>(args.v())) {
      return std::optional<Sum<Nat, Nat>>();
    } else {
      const auto &[a0, a1] = std::get<typename List<Nat>::Cons>(args.v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<Nat>::Nil>(_sv.v())) {
        return std::make_optional<Sum<Nat, Nat>>(
            Sum<Nat, Nat>::inl(a0.add(a0)));
      } else {
        return std::optional<Sum<Nat, Nat>>();
      }
    }
  };

  template <Params _tcI0, typename T1>
  static semantic_function<typename _tcI0::ptr, T1>
  my_vastart(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h) {
    return [=](const List<Nat> &args,
               const std::optional<typename _tcI0::ptr> &varargs)
               -> Itree<T1, Sum<Nat, Nat>> {
      if (std::holds_alternative<typename List<Nat>::Nil>(args.v())) {
        return to_itree<T1>(h, std::optional<Sum<Nat, Nat>>());
      } else {
        const auto &[a0, a1] = std::get<typename List<Nat>::Cons>(args.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<Nat>::Nil>(_sv.v())) {
          if (varargs.has_value()) {
            const typename _tcI0::ptr &_x = *varargs;
            return Itree<T1, Sum<Nat, Nat>>::go(
                ItreeF<T1, Sum<Nat, Nat>, Itree<T1, Sum<Nat, Nat>>>::retf(
                    Sum<Nat, Nat>::inl(a0)));
          } else {
            return to_itree<T1>(h, std::optional<Sum<Nat, Nat>>());
          }
        } else {
          return to_itree<T1>(h, std::optional<Sum<Nat, Nat>>());
        }
      }
    };
  }

  template <Params _tcI0, typename T1>
  static intrinsic_definitions<typename _tcI0::ptr, T1>
  defined(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h) {
    return List<
        std::pair<Nat, crane::fn<Itree<T1, Sum<Nat, Nat>>(
                           List<Nat>, std::optional<typename _tcI0::ptr>)>>>::
        cons(
            std::make_pair(Nat::s(Nat::o()),
                           pure_to_semantic<_tcI0, T1>(h, p1)),
            List<std::pair<
                Nat, crane::fn<Itree<T1, Sum<Nat, Nat>>(
                         List<Nat>, std::optional<typename _tcI0::ptr>)>>>::
                cons(
                    std::make_pair(Nat::s(Nat::s(Nat::o())),
                                   pure_to_semantic<_tcI0, T1>(h, p2)),
                    List<std::pair<
                        Nat,
                        crane::fn<Itree<T1, Sum<Nat, Nat>>(
                            List<Nat>, std::optional<typename _tcI0::ptr>)>>>::
                        cons(
                            std::make_pair(Nat::s(Nat::s(Nat::s(Nat::o()))),
                                           pure_to_semantic<_tcI0, T1>(h, p1)),
                            List<std::pair<
                                Nat,
                                crane::fn<Itree<T1, Sum<Nat, Nat>>(
                                    List<Nat>,
                                    std::optional<typename _tcI0::ptr>)>>>::
                                cons(
                                    std::make_pair(
                                        Nat::s(
                                            Nat::s(Nat::s(Nat::s(Nat::o())))),
                                        pure_to_semantic<_tcI0, T1>(h, p2)),
                                    List<std::pair<
                                        Nat, crane::fn<Itree<T1, Sum<Nat, Nat>>(
                                                 List<Nat>,
                                                 std::optional<
                                                     typename _tcI0::ptr>)>>>::
                                        cons(
                                            std::make_pair(
                                                Nat::s(Nat::s(Nat::s(
                                                    Nat::s(Nat::s(Nat::o()))))),
                                                my_vastart<_tcI0, T1>(h)),
                                            List<std::pair<
                                                Nat, crane::fn<Itree<
                                                         T1, Sum<Nat, Nat>>(
                                                         List<Nat>,
                                                         std::optional<
                                                             typename _tcI0::
                                                                 ptr>)>>>::
                                                cons(
                                                    std::make_pair(
                                                        Nat::s(Nat::s(Nat::s(
                                                            Nat::s(Nat::s(Nat::s(
                                                                Nat::o())))))),
                                                        pure_to_semantic<
                                                            _tcI0, T1>(h, p1)),
                                                    List<std::pair<
                                                        Nat,
                                                        crane::fn<Itree<
                                                            T1, Sum<Nat, Nat>>(
                                                            List<Nat>,
                                                            std::optional<
                                                                typename _tcI0::
                                                                    ptr>)>>>::
                                                        nil()))))));
  }

  struct natParams {
    using ptr = Nat;

    static Nat zero() { return Nat::o(); }
  };

  static_assert(Params<natParams>);
  static inline const Nat count =
      defined<natParams, FailE>(
          CategoryOps::template ReSum_id<crane::obj,
                                         crane::fn<crane::obj(crane::obj)>>(
              [](crane::obj) {
                return crane_erase_fn<crane::obj>(Function::Id_IFun);
              },
              crane::obj()))
          .length();
  static inline const bool is_six =
      count.eqb(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))));
};

template <typename T1, typename T2>
T2 CategoryOps::id_(std::type_identity_t<Id_<T1, T2>> id_0, T1 x0_) {
  return id_0(std::move(x0_));
}

template <typename T1, typename T2>
T2 CategoryOps::resum(const T1 &, const T1 &, T2 reSum) {
  return reSum;
}

template <typename T1, typename T2>
ReSum<T1, T2> CategoryOps::ReSum_id(std::type_identity_t<Id_<T1, T2>> x0_,
                                    const T1 &x1_) {
  return CategoryOps::template id_<T1, T2>(std::move(x0_), x1_);
}

template <typename T1, typename T2, typename T3>
crane::rebind_t<T2, T3>
Subevent::subevent(ReSum<crane::obj, IFun<crane::obj, crane::obj>> h,
                   crane::rebind_t<T1, T3> x) {
  return crane_any_cast<crane::rebind_t<T2, T3>>(
      CategoryOps::resum(crane::obj(), crane::obj(), h)(std::move(x)));
}

#endif // INCLUDED_INTRINSIC_TABLE_CURRY
