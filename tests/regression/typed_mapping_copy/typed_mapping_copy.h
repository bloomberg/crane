#pragma once

#include <array>
#include <cstdint>
#include <memory>
#include <optional>
#include <vector>

struct TypedMappingCopy {
  static bool flag_both(bool a, bool b);
  static uint64_t bag_count(const std::vector<uint64_t> &b);
  static bool cell_flag(std::array<bool, 1> c);
  static uint64_t cell_bag_count(const std::array<std::vector<uint64_t>, 1> &c);
  static std::array<std::vector<uint64_t>, 1> make_cell(uint64_t n);
  static bool flag_of_option(const std::optional<bool> &o);
  static std::vector<uint64_t> bag_of_option(const std::optional<uint64_t> &o);
};
