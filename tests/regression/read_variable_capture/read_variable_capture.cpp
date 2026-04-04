#include <read_variable_capture.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <type_traits>

/// Works: literal argument — no capture needed
std::string ReadVariableCapture::read_literal() {
  return [&]() -> std::string {
    std::ifstream file("file.txt"s);
    if (!file) {
      std::cerr << "Failed to open file " << "file.txt"s << '\n';
      return std::string{};
    }
    return std::string(std::istreambuf_iterator<char>(file),
                       std::istreambuf_iterator<char>());
  }();
}

/// Bug: variable argument — path not captured by []() { ... path ... }()
std::string ReadVariableCapture::read_variable(const std::string path) {
  return [&]() -> std::string {
    std::ifstream file(path);
    if (!file) {
      std::cerr << "Failed to open file " << path << '\n';
      return std::string{};
    }
    return std::string(std::istreambuf_iterator<char>(file),
                       std::istreambuf_iterator<char>());
  }();
}

/// Bug: same issue with file_exists which is std::filesystem::exists(...),
/// but that's a plain expression, not a lambda, so it works.
/// This test is for read specifically.
std::string ReadVariableCapture::read_and_check(const std::string path) {
  bool ok = std::filesystem::exists(std::filesystem::path(path));
  if (ok) {
    return [&]() -> std::string {
      std::ifstream file(path);
      if (!file) {
        std::cerr << "Failed to open file " << path << '\n';
        return std::string{};
      }
      return std::string(std::istreambuf_iterator<char>(file),
                         std::istreambuf_iterator<char>());
    }();
  } else {
    return "";
  }
}
