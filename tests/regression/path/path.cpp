#include "path.h"

std::string Path::abs_path(const std::string &p) {
  return [&]() -> std::string {
    std::error_code _ec;
    auto _r = std::filesystem::absolute(std::filesystem::path(p), _ec);
    return _ec ? std::string{} : _r.string();
  }();
}

std::string Path::canon_path(const std::string &p) {
  return [&]() -> std::string {
    std::error_code _ec;
    auto _r = std::filesystem::canonical(std::filesystem::path(p), _ec);
    return _ec ? std::string{} : _r.string();
  }();
}

std::string Path::rel_path(const std::string &p) {
  return [&]() -> std::string {
    std::error_code _ec;
    auto _r = std::filesystem::relative(std::filesystem::path(p), _ec);
    return _ec ? std::string{} : _r.string();
  }();
}

bool Path::check_is_dir(const std::string &p) {
  return [&]() -> bool {
    std::error_code _ec;
    return std::filesystem::is_directory(std::filesystem::path(p), _ec);
  }();
}

bool Path::check_is_file(const std::string &p) {
  return [&]() -> bool {
    std::error_code _ec;
    return std::filesystem::is_regular_file(std::filesystem::path(p), _ec);
  }();
}
