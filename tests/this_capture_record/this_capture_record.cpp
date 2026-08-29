#include "this_capture_record.h"

ThisCaptureRecord::callback_rec
ThisCaptureRecord::tree_callbacks(ThisCaptureRecord::tree t, uint64_t flag) {
  if (flag <= 0) {
    return callback_rec{[=](uint64_t x) mutable { return (x + t.tree_sum()); },
                        [=](uint64_t x) mutable { return (x * t.tree_sum()); }};
  } else {
    uint64_t _x = flag - 1;
    return callback_rec{[=](uint64_t x) mutable { return (t.tree_sum() + x); },
                        [=](uint64_t) mutable { return t.tree_sum(); }};
  }
}

ThisCaptureRecord::tag ThisCaptureRecord::mk_tag(uint64_t n) {
  return tag::mktag(n);
}
