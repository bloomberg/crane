#include <cassert>
#include <hk_class_field_result_cast_to_concept.h>

int main() {
  assert(HkClassFieldResultCastToConcept::run.v().index() == 1);
  return 0;
}
