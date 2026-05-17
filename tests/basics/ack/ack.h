#ifndef INCLUDED_ACK
#define INCLUDED_ACK

struct Nat {
  static inline const unsigned int one = 1u;
};

struct Ack {
  static unsigned int ack(unsigned int m, unsigned int n);
};

#endif // INCLUDED_ACK
