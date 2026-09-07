#ifndef INCLUDED_INSTANCE_ALIAS
#define INCLUDED_INSTANCE_ALIAS

#include <concepts>
#include <utility>

/// A constant whose type is a class applied to arguments is treated purely as
/// an instance declaration: Crane emits static_assert(Monoid<dict, ...>) for
/// it but never emits dict itself, so every use is an undeclared identifier.
/// An instance bound to a record literal (rather than to another instance's
/// name) is emitted correctly, so it is the aliasing that is lost.

template <typename I, typename A>
concept Monoid = requires {
  { I::zero() } -> std::convertible_to<A>;
  { I::op(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<A>;
};

struct InstanceAlias {
  struct MNat {
    static uint64_t zero() { return UINT64_C(0); }

    static uint64_t op(uint64_t a0, uint64_t a1) { return (a0 + a1); }
  };

  static_assert(Monoid<MNat, uint64_t>);
  static_assert(Monoid<dict, uint64_t>);
  static inline const uint64_t test = dict::op(UINT64_C(3), UINT64_C(4));
};

#endif // INCLUDED_INSTANCE_ALIAS
