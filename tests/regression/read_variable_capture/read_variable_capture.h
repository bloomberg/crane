#pragma once

#include <filesystem>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>
#include <string_view>
#include <system_error>

struct ReadVariableCapture {
  /// Works: literal argument — no capture needed
  static std::string read_literal();
  /// Bug: variable argument — path not captured by []() { ... path ... }()
  static std::string read_variable(const std::string &path);
  /// Bug: same issue with file_exists which is std::filesystem::exists(...),
  /// but that's a plain expression, not a lambda, so it works.
  /// This test is for read specifically.
  static std::string read_and_check(const std::string &path);
};
