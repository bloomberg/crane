#ifndef INCLUDED_COIND_FAMILY_PARAM
#define INCLUDED_COIND_FAMILY_PARAM

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;

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
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

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
};

struct CoindFamilyParam {
  template <typename E, typename R, typename T> struct treeF {
    // TYPES
    struct RetF {
      R r;
    };

    struct TauF {
      T t;
    };

    struct VisF {
      E x;
      crane::fn<T(crane::obj)> e;
    };

    using variant_t = std::variant<RetF, TauF, VisF>;
    using crane_family_tag = void;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    treeF() {}

    explicit treeF(RetF _v) : v_(std::move(_v)) {}

    explicit treeF(TauF _v) : v_(std::move(_v)) {}

    explicit treeF(VisF _v) : v_(std::move(_v)) {}

    template <typename _U0, typename _U1, typename _U2>
    treeF(const treeF<_U0, _U1, _U2> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename treeF<_U0, _U1, _U2>::RetF>(
                    _other.v())) {
              const auto &[r] =
                  std::get<typename treeF<_U0, _U1, _U2>::RetF>(_other.v());
              return RetF{[&]() -> R {
                if constexpr (crane_convertible<R, const _U1 &>) {
                  return crane_convert<R>(r);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              if (std::holds_alternative<typename treeF<_U0, _U1, _U2>::TauF>(
                      _other.v())) {
                const auto &[t] =
                    std::get<typename treeF<_U0, _U1, _U2>::TauF>(_other.v());
                return TauF{[&]() -> T {
                  if constexpr (crane_convertible<T, const _U2 &>) {
                    return crane_convert<T>(t);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }()};
              } else {
                const auto &[x, e] =
                    std::get<typename treeF<_U0, _U1, _U2>::VisF>(_other.v());
                return VisF{[&]() -> E {
                              if constexpr (crane_convertible<E, const _U0 &>) {
                                return crane_convert<E>(x);
                              } else {
                                throw std::logic_error(
                                    "unreachable: inactive constructor field "
                                    "at this instantiation");
                              }
                            }(),
                            crane_convert<crane::fn<T(crane::obj)>>(e)};
              }
            }
          }()) {}

    static treeF<E, R, T> retf(R r) {
      return treeF<E, R, T>(RetF{std::move(r)});
    }

    static treeF<E, R, T> tauf(T t) {
      return treeF<E, R, T>(TauF{std::move(t)});
    }

    static treeF<E, R, T> visf(E x, crane::fn<T(crane::obj)> e) {
      return treeF<E, R, T>(VisF{std::move(x), std::move(e)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename E, typename R> struct tree {
    // TYPES
    template <typename _S0 = tree<E, R>> struct Go_ {
      treeF<E, R, _S0> observe;
    };

    using Go = Go_<>;
    using variant_t = std::variant<Go>;
    using crane_family_tag = void;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Go _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    template <typename _U0, typename _U1>
    tree(const tree<_U0, _U1> &_other)
        : lazy_v_(crane::lazy<variant_t>::converted_from(
              _other.lazy_cell(), [=]() -> variant_t {
                const auto &[observe] =
                    std::get<typename tree<_U0, _U1>::Go>(_other.v());
                return Go{crane_convert<treeF<E, R, tree<E, R>>>(observe)};
              })) {}

    explicit tree(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static tree<E, R> go(treeF<E, R, tree<E, R>> observe) {
      return tree<E, R>(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, std::move(observe)));
    }

    explicit tree(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static tree<E, R> lazy_(F &&thunk) {
      return tree<E, R>(
          crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  template <typename T1, typename T2>
  static treeF<T1, T2, tree<T1, T2>> observe(tree<T1, T2> t) {
    const auto &[observe1] = std::get<typename tree<T1, T2>::Go>(t.v());
    return observe1;
  }

  struct voidE {
    voidE() = delete;
  };

  static tree<voidE, Nat> count(const Nat &n, const Nat &acc);
  static std::optional<Nat> run(const Nat &fuel, tree<voidE, Nat> t);
  static inline const std::optional<Nat> result = []() {
    auto _lit0 = Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
        Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
            Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                Nat::s(Nat::s(Nat::s(Nat::o()))))))))))))))))))))))))))))));
    auto _lit1 = Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
        Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
            Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                Nat::s(Nat::s(std::move(_lit0)))))))))))))))))))))))))))))));
    auto _lit2 = Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
        Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
            Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                Nat::s(Nat::s(std::move(_lit1)))))))))))))))))))))))))))))));
    return run(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                   Nat::s(Nat::s(Nat::s(Nat::s(std::move(_lit2))))))))))),
               count(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                         Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))))))),
                     Nat::o()));
  }();
  static inline const bool is_ten = []() -> bool {
    if (result.has_value()) {
      const Nat &n = *result;
      return n.eqb(Nat::s(Nat::s(Nat::s(
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))))))));
    } else {
      return false;
    }
  }();
};

#endif // INCLUDED_COIND_FAMILY_PARAM
