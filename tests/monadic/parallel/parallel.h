#ifndef INCLUDED_PARALLEL
#define INCLUDED_PARALLEL

#include <future>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

struct Nat {
  static inline const unsigned int one = 1u;
};

struct ParallelTest {
  static unsigned int ack(const std::pair<unsigned int, unsigned int> &p);
  static std::pair<unsigned int, unsigned int> fast(const unsigned int m,
                                                    unsigned int n);
  static std::pair<unsigned int, unsigned int> slow(const unsigned int m,
                                                    unsigned int n);
};

#endif // INCLUDED_PARALLEL
