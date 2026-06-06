#ifndef INCLUDED_RECORD_USE_AFTER_MOVE
#define INCLUDED_RECORD_USE_AFTER_MOVE

#include <utility>

struct RecordUseAfterMove {
  struct box {
    uint64_t payload;
    bool enabled;
  };

  static box clone_box(const box &b);
  static box keep_box(box b);
  static uint64_t use_box(const box &b);
  static inline const box initial_box = box{UINT64_C(41), true};
  /// BUG: The same shared_ptr local b is moved into multiple call sites.
  /// After the first std::move(b), subsequent uses dereference a
  /// moved-from shared_ptr, causing a segfault.
  static inline const box problematic = []() {
    box b = keep_box(initial_box);
    box b1 = clone_box(b);
    box b2 = clone_box(b);
    if (keep_box(b).enabled) {
      if (std::move(b).enabled) {
        return b2;
      } else {
        return b1;
      }
    } else {
      return b1;
    }
  }();
  /// Simple case: same record used twice in let bindings.
  static inline const uint64_t double_let = []() {
    uint64_t x = initial_box.payload;
    uint64_t y = initial_box.payload;
    return (x + y);
  }();
  /// Record passed to two different functions.
  static inline const uint64_t two_consumers = []() {
    uint64_t p = use_box(initial_box);
    uint64_t q = use_box(initial_box);
    return (p + q);
  }();
};

#endif // INCLUDED_RECORD_USE_AFTER_MOVE
