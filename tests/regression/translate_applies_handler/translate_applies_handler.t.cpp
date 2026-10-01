#include "translate_applies_handler.h"
#include <cassert>

int main() {
  assert(TranslateAppliesHandler::relabelled_event == 1);
  assert(TranslateAppliesHandler::injected_side == 2);
  return 0;
}
