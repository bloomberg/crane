#ifndef INCLUDED_LAST_USE_PLACES
#define INCLUDED_LAST_USE_PLACES

#include <big_support.h>
#include <cstdint>
#include <utility>

struct LastUsePlaces {
  static std::pair<Big, Big> split(uint64_t n);
  /// Each member of the dead local q read once: both move.
  static std::pair<Big, Big> swap_fields(uint64_t n);
  /// b read twice, whole: neither read may move.
  static std::pair<Big, Big> twice(uint64_t n);
  /// A member of q and q itself: neither may move.
  static std::pair<Big, std::pair<Big, Big>> both(uint64_t n);
  /// A template that splices its argument twice.
  static uint64_t dup(uint64_t n);
};

#endif // INCLUDED_LAST_USE_PLACES
