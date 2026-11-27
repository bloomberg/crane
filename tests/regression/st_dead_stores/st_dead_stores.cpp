#include "st_dead_stores.h"

uint64_t written_only() {
  uint64_t _lc1_k = UINT64_C(3);
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _lc1_loop_k = _lc1_k;
  while (true) {
    if (_lc1_loop_k <= 0) {
      return UINT64_C(7);
    } else {
      uint64_t k_ = _lc1_loop_k - 1;
      _lc1_loop_k = k_;
    }
  }
}

uint64_t read_by_dead_store() {
  uint64_t _lc1_k = UINT64_C(4);
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _lc1_loop_k = _lc1_k;
  while (true) {
    if (_lc1_loop_k <= 0) {
      return _lc1_loop_k;
    } else {
      uint64_t k_ = _lc1_loop_k - 1;
      _lc1_loop_k = k_;
    }
  }
}

uint64_t written_in_branch(bool b) {
  uint64_t x = [&]() -> uint64_t {
    if (b) {
      return UINT64_C(1);
    } else {
      return UINT64_C(2);
    }
  }();
  return x + UINT64_C(10);
}

uint64_t written_in_unused_branch(bool b) {
  uint64_t s = UINT64_C(3);
  [&]() -> uint64_t {
    if (b) {
      s = (s + UINT64_C(1));
      return UINT64_C(1);
    } else {
      return UINT64_C(2);
    }
  }();
  return s;
}

uint64_t STDeadStores::written_in_branch(bool b) {
  return ::written_in_branch(b);
}

uint64_t STDeadStores::written_in_unused_branch(bool b) {
  return ::written_in_unused_branch(b);
}
