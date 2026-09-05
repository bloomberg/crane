#ifndef INCLUDED_NAT_LITERAL_OVERFLOW
#define INCLUDED_NAT_LITERAL_OVERFLOW

struct NatLiteralOverflow {
  /// A nat literal too large for the 64-bit integer nat maps onto is
  /// emitted verbatim, producing an out-of-range C++ literal with no
  /// diagnostic from Crane.
  static inline const uint64_t big = UINT64_C(18446744073709551616);
  static inline const uint64_t bigger = UINT64_C(100000000000000000000000);
  static inline const uint64_t small = UINT64_C(5);
  static inline const uint64_t total = (big + small);
  static inline const bool wraps = big == UINT64_C(0);
};

#endif // INCLUDED_NAT_LITERAL_OVERFLOW
