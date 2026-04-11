#include <record_use_after_move.h>

#include <memory>
#include <type_traits>
#include <utility>

std::shared_ptr<RecordUseAfterMove::box>
RecordUseAfterMove::clone_box(std::shared_ptr<RecordUseAfterMove::box> b) {
  return std::make_shared<RecordUseAfterMove::box>(box{b->payload, b->enabled});
}

std::shared_ptr<RecordUseAfterMove::box>
RecordUseAfterMove::keep_box(std::shared_ptr<RecordUseAfterMove::box> b) {
  return b;
}

__attribute__((pure)) unsigned int
RecordUseAfterMove::use_box(const std::shared_ptr<RecordUseAfterMove::box> &b) {
  return b->payload;
}
