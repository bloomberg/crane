#include "vector_capacity.h"

/// A fresh vector filled by a counted loop, one append per iteration, has
/// its capacity reserved from the loop's count; any other filling shape is
/// left to grow as it would.
/// Reserved: exactly n appends.
std::vector<uint64_t> VectorCapacity::fill(uint64_t n) {
  std::vector<uint64_t> v = {};
  {
    uint64_t _lc1_k = n;
    uint64_t _lc1_loop_k = _lc1_k;
    (_lc1_loop_k <= v.max_size() ? v.reserve(_lc1_loop_k) : void());
    while (true) {
      if (_lc1_loop_k <= 0) {
        return v;
      } else {
        uint64_t k_ = _lc1_loop_k - 1;
        v.push_back(_lc1_loop_k);
        _lc1_loop_k = k_;
      }
    }
  }
}

/// Not reserved: the append is conditional.
std::vector<uint64_t> VectorCapacity::fill_even(uint64_t n) {
  std::vector<uint64_t> v = {};
  {
    uint64_t _lc1_k = n;
    uint64_t _lc1_loop_k = _lc1_k;
    while (true) {
      if (_lc1_loop_k <= 0) {
        return v;
      } else {
        uint64_t k_ = _lc1_loop_k - 1;
        [&]() -> void {
          if (Nat::even(_lc1_loop_k)) {
            v.push_back(_lc1_loop_k);
            return;
          } else {
            return;
          }
        }();
        _lc1_loop_k = k_;
      }
    }
  }
}

/// Not reserved: two appends an iteration.
std::vector<uint64_t> VectorCapacity::fill_twice(uint64_t n) {
  std::vector<uint64_t> v = {};
  {
    uint64_t _lc1_k = n;
    uint64_t _lc1_loop_k = _lc1_k;
    while (true) {
      if (_lc1_loop_k <= 0) {
        return v;
      } else {
        uint64_t k_ = _lc1_loop_k - 1;
        v.push_back(_lc1_loop_k);
        v.push_back(_lc1_loop_k);
        _lc1_loop_k = k_;
      }
    }
  }
}

/// Not reserved: the loop can stop early.
std::vector<uint64_t> VectorCapacity::fill_until_five(uint64_t n) {
  std::vector<uint64_t> v = {};
  {
    uint64_t _lc1_k = n;
    uint64_t _lc1_loop_k = _lc1_k;
    while (true) {
      if (_lc1_loop_k <= 0) {
        return v;
      } else {
        uint64_t k_ = _lc1_loop_k - 1;
        if (_lc1_loop_k == UINT64_C(5)) {
          return v;
        } else {
          v.push_back(_lc1_loop_k);
          _lc1_loop_k = k_;
        }
      }
    }
  }
}

bool Nat::even(uint64_t n) {
  if (n <= 0) {
    return true;
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return false;
    } else {
      uint64_t n_ = n0 - 1;
      return Nat::even(n_);
    }
  }
}
