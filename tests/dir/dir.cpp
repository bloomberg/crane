#include "dir.h"

bool Dir::make_dir(std::string path) {
  return [&]() -> bool {
    std::error_code _ec;
    std::filesystem::create_directories(std::filesystem::path(path), _ec);
    return !_ec;
  }();
}

bool Dir::remove_dir(std::string path) {
  return [&]() -> bool {
    std::error_code _ec;
    std::filesystem::remove_all(std::filesystem::path(path), _ec);
    return !_ec;
  }();
}

std::string Dir::get_cwd() {
  return [&]() -> std::string {
    std::error_code _ec;
    auto _p = std::filesystem::current_path(_ec);
    return _ec ? std::string{} : _p.string();
  }();
}

List<std::string> Dir::list_dir(std::string path) {
  return [&]() -> List<std::string> {
    auto result = List<std::string>::nil();
    std::error_code _ec;
    std::size_t _count = 0;
    std::filesystem::directory_iterator _it(std::filesystem::path(path), _ec),
        _end;
    for (; !_ec && _it != _end && _count < 65536;
         _it.increment(_ec), ++_count) {
      result = List<std::string>::cons(_it->path().filename().string(),
                                       std::move(result));
    }
    return result;
  }();
}
