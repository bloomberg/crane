#include "coind_projection_borrow.h"

/// A stream returned by value: a call to it is a temporary receiver.
CoindProjectionBorrow::Stream::stream
CoindProjectionBorrow::skip2(const CoindProjectionBorrow::Stream::stream &s) {
  return s.tl().tl();
}

/// Projections whose receivers are temporaries.
uint64_t
CoindProjectionBorrow::third(const CoindProjectionBorrow::Stream::stream &s) {
  return skip2(s).hd();
}

/// Projections whose receiver is a parameter, an lvalue.
uint64_t
CoindProjectionBorrow::sum_two(const CoindProjectionBorrow::Stream::stream &s) {
  return (s.hd() + s.tl().hd());
}
