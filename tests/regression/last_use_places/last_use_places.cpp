#include "last_use_places.h"

std::pair<Big, Big> LastUsePlaces::split(uint64_t n) {
  return std::make_pair(Big(n), Big((n + 1)));
}

/// Each member of the dead local q read once: both move.
std::pair<Big, Big> LastUsePlaces::swap_fields(uint64_t n) {
  std::pair<Big, Big> q = split(n);
  return std::make_pair(std::move(q).second, std::move(q).first);
}

/// b read twice, whole: neither read may move.
std::pair<Big, Big> LastUsePlaces::twice(uint64_t n) {
  Big b = Big(n);
  return std::make_pair(b, b);
}

/// A member of q and q itself: neither may move.
std::pair<Big, std::pair<Big, Big>> LastUsePlaces::both(uint64_t n) {
  std::pair<Big, Big> q = split(n);
  return std::make_pair(q.first, q);
}

/// A template that splices its argument twice.
uint64_t LastUsePlaces::dup(uint64_t n) {
  Big b = Big(n);
  return sum_twice(b, b);
}
