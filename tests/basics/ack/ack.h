#ifndef INCLUDED_ACK
#define INCLUDED_ACK

#include <memory>
#include <optional>
#include <type_traits>

struct Nat {
  static inline const unsigned int one = 1u;
};

struct Ack {
  static unsigned int ack(const unsigned int m, const unsigned int n);
};

#endif // INCLUDED_ACK
