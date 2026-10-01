#ifndef INCLUDED_NESTED_SUM1_MATCH_LOSES_TYPE
#define INCLUDED_NESTED_SUM1_MATCH_LOSES_TYPE

#include "crane_fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename ptr> struct Dvalue;
enum class AE;
enum class BE;
enum class CE;
template <typename ptr> struct FailE;
struct natParams;
using ptr = crane::obj;
template <typename
I>concept Params = requires {
  typename I::ptr;
} && (requires {
  { I::nullp() } -> std::convertible_to<typename I::ptr>;
} || requires {
  { I::nullp } -> std::convertible_to<typename I::ptr>;
});

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
};

template <typename ptr> struct Dvalue {
  // TYPES
  struct DP {
    ptr a0;
  };

  struct DU {};

  using variant_t = std::variant<DP, DU>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Dvalue() {}

  explicit Dvalue(DP _v) : v_(std::move(_v)) {}

  explicit Dvalue(DU _v) : v_(_v) {}

  template <typename _U>
  Dvalue(const Dvalue<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Dvalue<_U>::DP>(_other.v())) {
            const auto &[a0] = std::get<typename Dvalue<_U>::DP>(_other.v());
            return DP{[&]() -> ptr {
              if constexpr (crane_convertible<ptr, const _U &>) {
                return crane_convert<ptr>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            return DU{};
          }
        }()) {}

  static Dvalue<ptr> dp(ptr a0) { return Dvalue<ptr>(DP{std::move(a0)}); }

  static Dvalue<ptr> du() { return Dvalue<ptr>(DU{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};
enum class AE { A0 };
enum class BE { B0 };
enum class CE { C0 };

template <typename ptr> struct FailE {
  // DATA
  Dvalue<ptr> a0;

  // ACCESSORS
  FailE<ptr> clone() const { return {a0}; }

  template <typename _U> operator FailE<_U>() const { return {a0}; }

  // CREATORS
  static FailE<ptr> fail(Dvalue<ptr> a0) { return {std::move(a0)}; }
};

template <typename ptr, typename x = void>
using CFGEtop =
    Sum1<AE, Sum1<BE, Sum1<CE, FailE<ptr>, crane::obj>, crane::obj>, x>;

template <Params _tcI0, typename T1>
std::optional<Dvalue<typename _tcI0::ptr>>
exc_of_event(CFGEtop<typename _tcI0::ptr, T1> e) {
  if (std::holds_alternative<typename Sum1<
          AE,
          Sum1<BE, Sum1<CE, FailE<typename _tcI0::ptr>, crane::obj>,
               crane::obj>,
          T1>::Inl1>(e.v())) {
    return std::optional<Dvalue<typename _tcI0::ptr>>();
  } else {
    const auto &[a0] = std::get<typename Sum1<
        AE,
        Sum1<BE, Sum1<CE, FailE<typename _tcI0::ptr>, crane::obj>, crane::obj>,
        T1>::Inr1>(e.v());
    if (std::holds_alternative<
            typename Sum1<BE, Sum1<CE, FailE<typename _tcI0::ptr>, crane::obj>,
                          crane::obj>::Inl1>(a0.v())) {
      return std::optional<Dvalue<typename _tcI0::ptr>>();
    } else {
      const auto &[a00] = std::get<
          typename Sum1<BE, Sum1<CE, FailE<typename _tcI0::ptr>, crane::obj>,
                        crane::obj>::Inr1>(a0.v());
      if (std::holds_alternative<
              typename Sum1<CE, FailE<typename _tcI0::ptr>, crane::obj>::Inl1>(
              a00.v())) {
        return std::optional<Dvalue<typename _tcI0::ptr>>();
      } else {
        const auto &[a01] = std::get<
            typename Sum1<CE, FailE<typename _tcI0::ptr>, crane::obj>::Inr1>(
            a00.v());
        const auto &[a02] = a01;
        return std::make_optional<Dvalue<typename _tcI0::ptr>>(a02);
      }
    }
  }
}

struct natParams {
  using ptr = Nat;

  static Nat nullp() { return Nat::o(); }
};

static_assert(Params<natParams>);

struct NestedSum1MatchLosesType {
  static inline const std::optional<Dvalue<typename natParams::ptr>> run =
      exc_of_event<natParams, std::monostate>(
          sum1_inr(sum1_inr(sum1_inr(FailE<Nat>::fail(Dvalue<Nat>::du())))));
};

#endif // INCLUDED_NESTED_SUM1_MATCH_LOSES_TYPE
