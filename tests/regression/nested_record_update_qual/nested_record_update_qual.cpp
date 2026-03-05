#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <nested_record_update_qual.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<NestedRecordUpdateQual::Shadow> NestedRecordUpdateQual::bump(
    const std::shared_ptr<NestedRecordUpdateQual::Shadow> &x) {
  return [&](void) {
    unsigned int n = x->Shadow::value;
    return std::make_shared<NestedRecordUpdateQual::Shadow>(Shadow{(n + 1)});
  }();
}
