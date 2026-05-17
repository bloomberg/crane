#include "record_use_after_move.h"

RecordUseAfterMove::box
RecordUseAfterMove::clone_box(const RecordUseAfterMove::box &b) {
  return box{b.payload, b.enabled};
}

RecordUseAfterMove::box
RecordUseAfterMove::keep_box(RecordUseAfterMove::box b) {
  return b;
}

uint64_t RecordUseAfterMove::use_box(const RecordUseAfterMove::box &b) {
  return b.payload;
}
