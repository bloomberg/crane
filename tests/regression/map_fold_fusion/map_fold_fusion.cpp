#include "map_fold_fusion.h"

/// A right fold of a map, fused into one traversal where both callbacks are
/// pure under declared meanings and the mapped list is used once.
/// Fused: a declared operation, partly applied, and a declared operation.
uint64_t MapFoldFusion::sum_succ(const MapFoldFusion::list<uint64_t> &l) {
  return foldr<uint64_t, uint64_t>(
      [](uint64_t x, uint64_t acc) { return ((UINT64_C(1) + x) + acc); },
      UINT64_C(0), l);
}

/// Fused: lambdas, and a reducer that is not associative -- the fold's
/// association is kept.
uint64_t MapFoldFusion::alt_double(const MapFoldFusion::list<uint64_t> &l) {
  return foldr<uint64_t, uint64_t>(
      [](uint64_t x, uint64_t acc) {
        auto &&_once1 = (x * UINT64_C(2));
        return (((_once1 - acc) > _once1 ? 0 : (_once1 - acc)));
      },
      UINT64_C(0), l);
}

/// Fused across element types: the fold walks the map's input.
uint64_t MapFoldFusion::count_big(const MapFoldFusion::list<uint64_t> &l) {
  return foldr<uint64_t, uint64_t>(
      [](uint64_t x, uint64_t acc) -> uint64_t {
        bool b = UINT64_C(2) < x;
        if (b) {
          return (acc + 1);
        } else {
          return acc;
        }
      },
      UINT64_C(0), l);
}

/// Declined: twice has no declared meaning.
uint64_t MapFoldFusion::twice(uint64_t x) { return (x + x); }

uint64_t MapFoldFusion::sum_twice(const MapFoldFusion::list<uint64_t> &l) {
  return foldr<uint64_t, uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
      UINT64_C(0), map<uint64_t, uint64_t>(twice, l));
}

/// Declined: the mapped list is used twice.
uint64_t MapFoldFusion::sum_and_length(const MapFoldFusion::list<uint64_t> &l) {
  MapFoldFusion::list<uint64_t> m = map<uint64_t, uint64_t>(
      [](uint64_t _x0) -> uint64_t { return (UINT64_C(3) * _x0); }, l);
  return (
      foldr<uint64_t, uint64_t>(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
          UINT64_C(0), m) +
      length<uint64_t>(m));
}
