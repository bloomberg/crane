#include "case_handler_concrete_result.h"
#include <cassert>

int main() {
  assert(CaseHandlerConcreteResult::handled_left == 1);
  assert(CaseHandlerConcreteResult::handled_right == 2);
  return 0;
}
