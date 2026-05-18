#ifndef INCLUDED_READ_VARIABLE_CAPTURE
#define INCLUDED_READ_VARIABLE_CAPTURE

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>

using namespace std::string_literals;

struct ReadVariableCapture {
  /// Works: literal argument — no capture needed
  static std::string read_literal();
  /// Bug: variable argument — path not captured by []() { ... path ... }()
  static std::string read_variable(std::string path);
  /// Bug: same issue with file_exists which is std::filesystem::exists(...),
  /// but that's a plain expression, not a lambda, so it works.
  /// This test is for read specifically.
  static std::string read_and_check(std::string path);
};

#endif // INCLUDED_READ_VARIABLE_CAPTURE
