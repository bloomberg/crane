#include <set_test_pin_update.h>

__attribute__((pure)) SetTestPinUpdate::state
SetTestPinUpdate::set_test_pin(const SetTestPinUpdate::state &s, bool v) {
  return state{s.acc, v};
}
