#include <record_use_after_move.h>

#include <type_traits>

__attribute__((pure)) RecordUseAfterMove::box
RecordUseAfterMove::clone_box(const RecordUseAfterMove::box &b) {
  return box{b.payload, b.enabled};
}

__attribute__((pure)) RecordUseAfterMove::box
RecordUseAfterMove::keep_box(RecordUseAfterMove::box b) {
  return b;
}

__attribute__((pure)) unsigned int
RecordUseAfterMove::use_box(const RecordUseAfterMove::box &b) {
  return b.payload;
}
