#ifndef INCLUDED_ACK
#define INCLUDED_ACK

struct Ack {
  static uint64_t ack(uint64_t m, uint64_t n);
};

struct Nat {
  static inline const uint64_t one = UINT64_C(1);
};

#endif // INCLUDED_ACK
