#include <dir.h>

#include <filesystem>
#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

bool Dir::make_dir(const std::string path) {
  return std::filesystem::create_directories(std::filesystem::path(path));
}

bool Dir::remove_dir(const std::string path) {
  return std::filesystem::remove_all(std::filesystem::path(path));
}

std::string Dir::get_cwd() { return std::filesystem::current_path().string(); }

List<std::string> Dir::list_dir(const std::string path) {
  return [&]() -> List<std::string> {
    auto result = List<std::string>::nil();
    for (const auto &entry : std::filesystem::directory_iterator(path)) {
      result = List<std::string>::cons(entry.path().filename().string(),
                                       std::move(result));
    }
    return result;
  }();
}
