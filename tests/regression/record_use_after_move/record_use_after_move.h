#ifndef INCLUDED_RECORD_USE_AFTER_MOVE
#define INCLUDED_RECORD_USE_AFTER_MOVE

#include <cstdint>
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
  static constexpr uint64_t double_let = UINT64_C(82);
  /// Record passed to two different functions.
  static constexpr uint64_t two_consumers = UINT64_C(82);
};

#endif // INCLUDED_RECORD_USE_AFTER_MOVE
