#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_test_pin_update.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int
SetTestPinUpdate::acc(const std::shared_ptr<SetTestPinUpdate::state> &s) {
  return s->acc;
}

bool SetTestPinUpdate::test_pin(
    const std::shared_ptr<SetTestPinUpdate::state> &s) {
  return s->test_pin;
}

std::shared_ptr<SetTestPinUpdate::state>
SetTestPinUpdate::set_test_pin(std::shared_ptr<SetTestPinUpdate::state> s,
                               const bool v) {
  return std::make_shared<SetTestPinUpdate::state>(
      state{std::move(s)->acc, std::move(v)});
}
