#include "read_variable_capture.h"

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
