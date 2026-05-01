#include <effect_list_return.h>

/// 1. list_directory returns a list
List<std::string> EffectListReturn::list_files(const std::string path) {
  return [&]() -> List<std::string> {
    auto result = List<std::string>::nil();
    for (const auto &entry : std::filesystem::directory_iterator(path)) {
      result = List<std::string>::cons(entry.path().filename().string(),
                                       std::move(result));
    }
    return result;
  }();
}

/// 2. create dir and verify
bool EffectListReturn::make_and_check(const std::string path) {
  return std::filesystem::create_directories(std::filesystem::path(path));
}

/// 3. get_time result used in pair
std::pair<int64_t, std::string> EffectListReturn::timestamped_line() {
  int64_t t = static_cast<int64_t>(
      std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::system_clock::now().time_since_epoch())
          .count());
  std::string line;
  std::getline(std::cin, line);
  return std::make_pair(t, line);
}

/// 4. current_path as a no-arg effect
std::string EffectListReturn::get_cwd() {
  return std::filesystem::current_path().string();
}

/// 5. Chain effects with different return types
std::pair<bool, List<std::string>>
EffectListReturn::create_and_list(const std::string dir) {
  bool ok = std::filesystem::create_directories(std::filesystem::path(dir));
  if (ok) {
    List<std::string> files = [&]() -> List<std::string> {
      auto result = List<std::string>::nil();
      for (const auto &entry : std::filesystem::directory_iterator(dir)) {
        result = List<std::string>::cons(entry.path().filename().string(),
                                         std::move(result));
      }
      return result;
    }();
    return std::make_pair(true, files);
  } else {
    return std::make_pair(false, List<std::string>::nil());
  }
}
