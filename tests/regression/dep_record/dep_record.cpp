#include <algorithm>
#include <any>
#include <cassert>
#include <dep_record.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

DepRecord::tag DepRecord::the_tag(const std::shared_ptr<DepRecord::Tagged> &t) {
  return t->the_tag;
}

DepRecord::tag_type
DepRecord::the_value(const std::shared_ptr<DepRecord::Tagged> &t) {
  return t->the_value;
}
