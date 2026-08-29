#ifndef INCLUDED_SPECIF
#define INCLUDED_SPECIF

#include <utility>
#include <variant>

namespace Specif {

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }

  P projT2() const {
    const auto &[x0, a1] = *this;
    return a1;
  }
};

} // namespace Specif

#endif // INCLUDED_SPECIF
