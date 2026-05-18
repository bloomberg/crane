#include "let_fix_hoisted_template.h"

List<uint64_t> LetFixHoistedTemplate::reverse_onto(const List<uint64_t> &l) {
  return _reverse_onto_go<uint64_t>(l, List<uint64_t>::nil());
}
