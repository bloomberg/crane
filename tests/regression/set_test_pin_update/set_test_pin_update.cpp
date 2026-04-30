#include <set_test_pin_update.h>

SetTestPinUpdate::state
SetTestPinUpdate::set_test_pin(const SetTestPinUpdate::state &s, bool v) {
  return state{s.acc, v};
}
