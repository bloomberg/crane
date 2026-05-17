#ifndef INCLUDED_ACK
#define INCLUDED_ACK

struct Nat {
  static inline const uint64_t one = UINT64_C(1);
};

struct Ack {
  static uint64_t ack(uint64_t m, uint64_t n);
};

#endif // INCLUDED_ACK
