#ifndef INCLUDED_PARALLEL
#define INCLUDED_PARALLEL

#include <functional>
#include <future>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct Nat {
  static inline const unsigned int one = 1u;
};

struct ParallelTest {
  static unsigned int ack(const std::pair<unsigned int, unsigned int> &p);
  static std::pair<unsigned int, unsigned int> fast(unsigned int m,
                                                    unsigned int n);
  static std::pair<unsigned int, unsigned int> slow(unsigned int m,
                                                    unsigned int n);
};

#endif // INCLUDED_PARALLEL
