#include <set_test_pin_update.h>

#include <memory>
#include <type_traits>
#include <utility>

std::shared_ptr<SetTestPinUpdate::state>
SetTestPinUpdate::set_test_pin(std::shared_ptr<SetTestPinUpdate::state> s,
                               const bool v) {
  return std::make_shared<SetTestPinUpdate::state>(
      state{std::move(s)->acc, std::move(v)});
}
