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

  A projT1() const {
    const auto &[x0, a1] = *this;
    return x0;
  }
};

} // namespace Specif

#endif // INCLUDED_SPECIF
