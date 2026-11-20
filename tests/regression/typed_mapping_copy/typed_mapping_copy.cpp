#include "typed_mapping_copy.h"

bool TypedMappingCopy::flag_both(bool a, bool b) {
  if (a) {
    return b;
  } else {
    return false;
  }
}

uint64_t TypedMappingCopy::bag_count(const std::vector<uint64_t> &b) {
  if (b.empty()) {
    return UINT64_C(0);
  } else {
    const uint64_t &x = b.front();
    return x;
  }
}

bool TypedMappingCopy::cell_flag(std::array<bool, 1> c) {
  const bool &f = c[0];
  return f;
}

uint64_t TypedMappingCopy::cell_bag_count(
    const std::array<std::vector<uint64_t>, 1> &c) {
  const std::vector<uint64_t> &b = c[0];
  return bag_count(b);
}

std::array<std::vector<uint64_t>, 1> TypedMappingCopy::make_cell(uint64_t n) {
  return std::array<std::vector<uint64_t>, 1>{std::vector<uint64_t>{n}};
}

bool TypedMappingCopy::flag_of_option(std::optional<bool> o) {
  if (o.has_value()) {
    const bool &f = *o;
    return f;
  } else {
    return false;
  }
}

std::vector<uint64_t>
TypedMappingCopy::bag_of_option(std::optional<uint64_t> o) {
  if (o.has_value()) {
    const uint64_t &n = *o;
    return std::vector<uint64_t>{n};
  } else {
    return std::vector<uint64_t>{};
  }
}
