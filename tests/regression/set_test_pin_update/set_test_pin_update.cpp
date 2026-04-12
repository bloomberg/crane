#include <set_test_pin_update.h>

#include <memory>
#include <type_traits>

std::shared_ptr<SetTestPinUpdate::state> SetTestPinUpdate::set_test_pin(
    const std::shared_ptr<SetTestPinUpdate::state> &s, const bool v) {
  return std::make_shared<SetTestPinUpdate::state>(state{s->acc, v});
}
