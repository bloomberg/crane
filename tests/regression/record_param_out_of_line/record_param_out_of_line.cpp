#include "record_param_out_of_line.h"

RecordParamOutOfLine::Bag::Kind
RecordParamOutOfLine::Bag::classify(const RecordParamOutOfLine::Bag &b) {
  if (b.full) {
    return Kind::LARGE;
  } else {
    return Kind::SMALL;
  }
}
