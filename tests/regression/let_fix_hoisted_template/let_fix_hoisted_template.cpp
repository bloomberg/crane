#include "let_fix_hoisted_template.h"

List<unsigned int>
LetFixHoistedTemplate::reverse_onto(const List<unsigned int> &l) {
  return _reverse_onto_go<unsigned int>(l, List<unsigned int>::nil());
}
