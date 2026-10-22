#ifndef INCLUDED_LOOPIFY_COERCED_SELF_CALL
#define INCLUDED_LOOPIFY_COERCED_SELF_CALL

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct Sig;

/// A recursive call made through a coercion of its callee is a recursive
/// call.
///
/// Nat.even_EvenT calls itself as (magic even_EvenT) n', the coercion
/// standing for the change of index in its result type, and the C++ calls
/// even_EvenT(n1) where it stands, below the frame that binds the result.
/// The recursion plan read only a callee written as a bare global, saw no
/// recursion, and the function was left calling itself: half of two
/// million ran two million C++ frames deep.
struct LoopifyCoercedSelfCall {
  static uint64_t half(uint64_t n);
};

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  template <typename CraneU> operator Sig<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const A &>) {
        return crane_convert<CraneU>(x);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

struct Nat {
  using EvenT = Sig<uint64_t>;
  static inline const EvenT EvenT_0 = Sig<uint64_t>::exist(UINT64_C(0));
  static EvenT EvenT_2(uint64_t _x, const Sig<uint64_t> &h0);
  static EvenT even_EvenT(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_COERCED_SELF_CALL
