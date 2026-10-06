#ifndef INCLUDED_TFUNCTOR_OPTION_INSTANCE
#define INCLUDED_TFUNCTOR_OPTION_INSTANCE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
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

struct TfunctorOptionInstance {
  template <TFunctor _tcI0, typename T2, typename T3, typename F0>
  static typename _tcI0::template T<T3>
  tfmap(F0 &&f, typename _tcI0::template T<T2> x) {
    return _tcI0::template tfmap<T2, T3>(f, std::move(x));
  }

  template <TFunctor _tcI0> struct TFunctor_option {
    template <typename CraneA0>
    using T = std::optional<typename _tcI0::template T<CraneA0>>;

    template <typename CraneA0, typename CraneA1>
    static std::optional<typename _tcI0::template T<CraneA1>>
    tfmap(crane::fn<CraneA1(CraneA0)> f,
          std::optional<typename _tcI0::template T<CraneA0>> ot) {
      if (ot.has_value()) {
        const typename _tcI0::template T<CraneA0> &t = *ot;
        return std::make_optional<typename _tcI0::template T<CraneA1>>(
            _tcI0::template tfmap<CraneA0, CraneA1>(std::move(f), t));
      } else {
        return std::optional<typename _tcI0::template T<CraneA1>>();
      }
    }
  };

  template <typename T> struct box {
    T unbox;

    // ACCESSORS
    template <typename CraneU> operator box<CraneU>() const {
      return {[&]() -> CraneU {
        if constexpr (crane_convertible<CraneU, const T &>) {
          return crane_convert<CraneU>(unbox);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }
  };

  struct TFunctor_box {
    template <typename CraneA0> using T = box<CraneA0>;

    template <typename CraneA0, typename CraneA1>
    static box<CraneA1> tfmap(crane::fn<CraneA1(CraneA0)> f, box<CraneA0> b) {
      return box<CraneA1>{f(std::move(b).unbox)};
    }
  };

  static_assert(TFunctor<TFunctor_box>);
  static inline const std::optional<box<Nat>> o =
      TFunctor_option<TFunctor_box>::template tfmap<Nat, Nat>(
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
