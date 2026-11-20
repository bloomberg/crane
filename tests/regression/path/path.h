#pragma once

#include <filesystem>
#include <string>
#include <string_view>
#include <system_error>

struct Path {
  static std::string abs_path(const std::string &p);
  static std::string canon_path(const std::string &p);
  static std::string rel_path(const std::string &p);
  static bool check_is_dir(const std::string &p);
  static bool check_is_file(const std::string &p);
};
