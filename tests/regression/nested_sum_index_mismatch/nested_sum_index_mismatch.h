#ifndef INCLUDED_NESTED_SUM_INDEX_MISMATCH
#define INCLUDED_NESTED_SUM_INDEX_MISMATCH

#include "crane_fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename E1, typename E2, typename X> struct Sum1;

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

template <typename E1, typename E2, typename X> struct Sum1 {
  // TYPES
  struct Inl1 {
    crane::rebind_t<E1, X> a0;
  };

  struct Inr1 {
    crane::rebind_t<E2, X> a0;
  };

  using variant_t = std::variant<Inl1, Inr1>;
  using crane_family_tag = void;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum1() {}

  explicit Sum1(Inl1 _v) : v_(std::move(_v)) {}

  explicit Sum1(Inr1 _v) : v_(std::move(_v)) {}

  template <typename _U0, typename _U1, typename _U2>
  Sum1(const Sum1<_U0, _U1, _U2> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum1<_U0, _U1, _U2>::Inl1>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Sum1<_U0, _U1, _U2>::Inl1>(_other.v());
            return Inl1{[&]() -> E1 {
              if constexpr (crane_convertible<E1, const _U0 &>) {
                return crane_convert<E1>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum1<_U0, _U1, _U2>::Inr1>(_other.v());
            return Inr1{[&]() -> E2 {
              if constexpr (crane_convertible<E2, const _U1 &>) {
                return crane_convert<E2>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Sum1<E1, E2, X> inl1(crane::rebind_t<E1, X> a0) {
    return Sum1<E1, E2, X>(Inl1{std::move(a0)});
  }

  static Sum1<E1, E2, X> inr1(crane::rebind_t<E2, X> a0) {
    return Sum1<E1, E2, X>(Inr1{std::move(a0)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct NestedSumIndexMismatch {
  enum class AE { A };
  enum class BE { B };

  struct cE {
    // DATA
    Nat a0;

    // ACCESSORS
    cE clone() const { return {a0}; }

    // CREATORS
    static cE c(Nat a0) { return {std::move(a0)}; }
  };

  template <typename x> using AllE = Sum1<AE, Sum1<BE, cE, crane::obj>, x>;

  template <typename T1>
  static std::optional<Nat>
  c_of(const Sum1<AE, Sum1<BE, cE, crane::obj>, T1> &e) {
    if (std::holds_alternative<
            typename Sum1<AE, Sum1<BE, cE, crane::obj>, T1>::Inl1>(e.v())) {
      return std::optional<Nat>();
    } else {
      const auto &[a0] =
          std::get<typename Sum1<AE, Sum1<BE, cE, crane::obj>, T1>::Inr1>(
              e.v());
      if (std::holds_alternative<typename Sum1<BE, cE, crane::obj>::Inl1>(
              a0.v())) {
        return std::optional<Nat>();
      } else {
        const auto &[a00] =
            std::get<typename Sum1<BE, cE, crane::obj>::Inr1>(a0.v());
        const auto &_sv1 = crane::any_cast<cE>(a00);
        const auto &[a01] = _sv1;
        return std::make_optional<Nat>(a01);
      }
    }
  }

  static inline const bool is_three = []() -> bool {
    auto _cs = c_of<std::monostate>(
        Sum1<AE, Sum1<BE, cE, crane::obj>, std::monostate>::inr1(
            Sum1<BE, cE, std::monostate>::inr1(
                cE::c(Nat::s(Nat::s(Nat::s(Nat::o())))))));
    if (_cs.has_value()) {
      const Nat &n = *_cs;
      return n.eqb(Nat::s(Nat::s(Nat::s(Nat::o()))));
    } else {
      return false;
    }
  }();
};

#endif // INCLUDED_NESTED_SUM_INDEX_MISMATCH
