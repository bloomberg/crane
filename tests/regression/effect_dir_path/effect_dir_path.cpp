#include <effect_dir_path.h>

/// 1. list_directory result matched — exercises IIFE + list match
std::optional<std::string> EffectDirPath::first_file(const std::string path) {
  List<std::string> files = [&]() -> List<std::string> {
    auto result = List<std::string>::nil();
    for (const auto &entry : std::filesystem::directory_iterator(path)) {
      result = List<std::string>::cons(entry.path().filename().string(),
                                       std::move(result));
    }
    return result;
  }();
  if (std::holds_alternative<typename List<std::string>::Nil>(files.v_mut())) {
    return std::optional<std::string>();
  } else {
    auto &[d_a0, d_a1] =
        std::get<typename List<std::string>::Cons>(files.v_mut());
    return std::make_optional<std::string>(d_a0);
  }
}

/// 2. current_path (zero args) chained to env
void EffectDirPath::save_cwd() {
  std::string cwd = std::filesystem::current_path().string();
  setenv("CWD"s.c_str(), cwd.c_str(), 1);
  return;
}

/// 3. is_directory bool result used in conditional with effects in arms
std::optional<std::string>
EffectDirPath::check_and_list(const std::string path) {
  bool isdir = std::filesystem::is_directory(std::filesystem::path(path));
  if (isdir) {
    return first_file(path);
  } else {
    return std::optional<std::string>();
  }
}

/// 4. Path effect result chained to print
void EffectDirPath::show_absolute(const std::string path) {
  std::string abs =
      std::filesystem::absolute(std::filesystem::path(path)).string();
  std::cout << abs << '\n';
  return;
}

/// 5. Multiple bool effects composed
std::string EffectDirPath::classify_path(const std::string path) {
  bool isdir = std::filesystem::is_directory(std::filesystem::path(path));
  bool isfile = std::filesystem::is_regular_file(std::filesystem::path(path));
  if (isdir) {
    return "directory";
  } else {
    if (isfile) {
      return "file";
    } else {
      return "other";
    }
  }
}

/// 6. create_directory bool result explicitly bound and used
std::string EffectDirPath::create_and_report(const std::string path) {
  bool ok = std::filesystem::create_directories(std::filesystem::path(path));
  if (ok) {
    std::cout << "Created"s << '\n';
    return "created";
  } else {
    std::cout << "Already exists"s << '\n';
    return "exists";
  }
}

/// 7. Recursive function counting list items from list_directory
unsigned int EffectDirPath::count_entries(const List<std::string> &dirs,
                                          unsigned int acc) {
  if (std::holds_alternative<typename List<std::string>::Nil>(dirs.v())) {
    return acc;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<std::string>::Cons>(dirs.v());
    List<std::string> files = [&]() -> List<std::string> {
      auto result = List<std::string>::nil();
      for (const auto &entry : std::filesystem::directory_iterator(d_a0)) {
        result = List<std::string>::cons(entry.path().filename().string(),
                                         std::move(result));
      }
      return result;
    }();
    unsigned int n = std::move(files).length();
    return count_entries(*(d_a1), (acc + n));
  }
}

/// 8. remove_directory (returns bool but treated as unit in bind)
void EffectDirPath::cleanup(const std::string path) {
  bool _x = std::filesystem::remove_all(std::filesystem::path(path));
  std::cout << "cleaned up"s << '\n';
  return;
}
