#ifndef INCLUDED_NAT_LITERAL_OVERFLOW
#define INCLUDED_NAT_LITERAL_OVERFLOW

struct NatLiteralOverflow {
  /// nat maps onto uint64_t, so a literal is only extractable if it fits.
  /// The largest one that does still comes through exactly.
  static inline const uint64_t max64 = UINT64_C(18446744073709551615);
  static inline const uint64_t small = UINT64_C(5);
  static inline const uint64_t total = (small + small);
};

#endif // INCLUDED_NAT_LITERAL_OVERFLOW
