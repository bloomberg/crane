#ifndef INCLUDED_TFUNCTOR_OPTION_INSTANCE
#define INCLUDED_TFUNCTOR_OPTION_INSTANCE

#include "crane_fn.h"
#include "fn.h"
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

struct TfunctorOptionInstance {
  template <typename t>
  using TFunctor = crane::fn<t(crane::fn<crane::obj(crane::obj)>, t)>;

  template <typename T1, typename T2, typename T3, typename F1>
  static crane::rebind_t<T1, T3>
  tfmap(std::type_identity_t<TFunctor<T1>> tFunctor, F1 &&f,
        crane::rebind_t<T1, T2> x) {
    return crane_container_cast<crane::rebind_t<T1, T3>>(
        tFunctor(crane_erase_fn(f), crane_convert<T1>(std::move(x))));
  }

  template <typename T1, typename F1>
  static std::optional<T1> TFunctor_option(std::type_identity_t<TFunctor<T1>> h,
                                           F1 &&f,
                                           const std::optional<T1> &ot) {
    if (ot.has_value()) {
      const auto &t = *ot;
      return std::make_optional<T1>(tfmap<T1, crane::obj, crane::obj>(h, f, t));
    } else {
      return std::optional<T1>();
    }
  }

  template <typename T> struct box {
    T unbox;

    // ACCESSORS
    template <typename _U> operator box<_U>() const {
      return {[&]() -> _U {
        if constexpr (crane_convertible<_U, const T &>) {
          return crane_convert<_U>(unbox);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }
  };

  static box<crane::obj> TFunctor_box(crane::fn<crane::obj(crane::obj)> f,
                                      const box<crane::obj> &b);
  static inline const std::optional<box<Nat>> o =
      tfmap<std::optional<box<crane::obj>>, Nat, Nat>(
          []() {
            return [](crane::fn<crane::obj(crane::obj)> _x0,
                      const auto &_x1) -> std::optional<box<crane::obj>> {
              return TFunctor_option<box<crane::obj>>(
                  [](auto &&_ec0, box<crane::obj> _ec1) {
                    return TFunctor_box(_ec0, _ec1);
                  },
                  _x0, crane_convert<std::optional<box<crane::obj>>>(_x1));
            };
          }(),
          [](const Nat &x) { return Nat::s(x); },
          std::make_optional<box<Nat>>(box<Nat>{Nat::s(Nat::s(Nat::o()))}));
  static inline const bool is_three = []() -> bool {
    if (o.has_value()) {
      const box<Nat> &b = *o;
      return b.unbox.eqb(Nat::s(Nat::s(Nat::s(Nat::o()))));
    } else {
      return false;
    }
  }();
};

#endif // INCLUDED_TFUNCTOR_OPTION_INSTANCE
