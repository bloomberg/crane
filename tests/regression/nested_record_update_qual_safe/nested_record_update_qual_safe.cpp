#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <nested_record_update_qual_safe.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<NestedRecordUpdateQualSafe::cell>
NestedRecordUpdateQualSafe::bump(
    const std::shared_ptr<NestedRecordUpdateQualSafe::cell> &x) {
  return [&](void) {
    unsigned int n = x->value;
    return std::make_shared<NestedRecordUpdateQualSafe::cell>(cell{(n + 1)});
  }();
}

unsigned int NestedRecordUpdateQualSafe::project(
    const std::shared_ptr<NestedRecordUpdateQualSafe::cell> &x) {
  return x->value;
}
