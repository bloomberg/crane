#include <qualified_record_shadow.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<QualifiedRecordShadow::Shadow> QualifiedRecordShadow::bump(
    const std::shared_ptr<QualifiedRecordShadow::Shadow> &x) {
  return [&](void) {
    unsigned int n = x->Shadow::value;
    return std::make_shared<QualifiedRecordShadow::Shadow>(Shadow{(n + 1)});
  }();
}
