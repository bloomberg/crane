#include "read_variable_capture.h"

/// Works: literal argument — no capture needed
std::string ReadVariableCapture::read_literal() {
  return [&]() -> std::string {
    std::ifstream file(std::string("file.txt"));
    if (!file) {
      std::cerr << "Failed to open file " << std::string("file.txt") << '\n';
      return std::string{};
    }
    return std::string(std::istreambuf_iterator<char>(file),
                       std::istreambuf_iterator<char>());
  }();
}

/// Bug: variable argument — path not captured by []() { ... path ... }()
std::string ReadVariableCapture::read_variable(std::string path) {
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
std::string ReadVariableCapture::read_and_check(std::string path) {
  bool ok = [&]() -> bool {
    std::error_code _ec;
    return std::filesystem::exists(std::filesystem::path(path), _ec);
  }();
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
