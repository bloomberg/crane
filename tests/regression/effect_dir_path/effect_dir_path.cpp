#include "effect_dir_path.h"

/// 1. list_directory result matched — exercises IIFE + list match
std::optional<std::string> EffectDirPath::first_file(std::string path) {
  List<std::string> files = [&]() -> List<std::string> {
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
  if (std::holds_alternative<typename List<std::string>::Nil>(files.v_mut())) {
    return std::optional<std::string>();
  } else {
    auto &[a0, a1] = std::get<typename List<std::string>::Cons>(files.v_mut());
    return std::make_optional<std::string>(a0);
  }
}

/// 2. current_path (zero args) chained to env
void EffectDirPath::save_cwd() {
  std::string cwd = [&]() -> std::string {
    std::error_code _ec;
    auto _p = std::filesystem::current_path(_ec);
    return _ec ? std::string{} : _p.string();
  }();
  setenv("CWD"s.c_str(), std::move(cwd).c_str(), 1);
  return;
}

/// 3. is_directory bool result used in conditional with effects in arms
std::optional<std::string> EffectDirPath::check_and_list(std::string path) {
  bool isdir = [&]() -> bool {
    std::error_code _ec;
    return std::filesystem::is_directory(std::filesystem::path(path), _ec);
  }();
  if (isdir) {
    return first_file(path);
  } else {
    return std::optional<std::string>();
  }
}

/// 4. Path effect result chained to print
void EffectDirPath::show_absolute(std::string path) {
  std::string abs = [&]() -> std::string {
    std::error_code _ec;
    auto _r = std::filesystem::absolute(std::filesystem::path(path), _ec);
    return _ec ? std::string{} : _r.string();
  }();
  std::cout << std::move(abs) << '\n';
  return;
}

/// 5. Multiple bool effects composed
std::string EffectDirPath::classify_path(std::string path) {
  bool isdir = [&]() -> bool {
    std::error_code _ec;
    return std::filesystem::is_directory(std::filesystem::path(path), _ec);
  }();
  bool isfile = [&]() -> bool {
    std::error_code _ec;
    return std::filesystem::is_regular_file(std::filesystem::path(path), _ec);
  }();
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
std::string EffectDirPath::create_and_report(std::string path) {
  bool ok = [&]() -> bool {
    std::error_code _ec;
    std::filesystem::create_directories(std::filesystem::path(path), _ec);
    return !_ec;
  }();
  if (ok) {
    std::cout << "Created"s << '\n';
    return "created";
  } else {
    std::cout << "Already exists"s << '\n';
    return "exists";
  }
}

/// 7. Recursive function counting list items from list_directory
uint64_t EffectDirPath::count_entries(const List<std::string> &dirs,
                                      uint64_t acc) {
  if (std::holds_alternative<typename List<std::string>::Nil>(dirs.v())) {
    return acc;
  } else {
    const auto &[a0, a1] = std::get<typename List<std::string>::Cons>(dirs.v());
    List<std::string> files = [&]() -> List<std::string> {
      auto result = List<std::string>::nil();
      std::error_code _ec;
      std::size_t _count = 0;
      std::filesystem::directory_iterator _it(std::filesystem::path(a0), _ec),
          _end;
      for (; !_ec && _it != _end && _count < 65536;
           _it.increment(_ec), ++_count) {
        result = List<std::string>::cons(_it->path().filename().string(),
                                         std::move(result));
      }
      return result;
    }();
    uint64_t n = std::move(files).length();
    return count_entries(*a1, (acc + n));
  }
}

/// 8. remove_directory (returns bool but treated as unit in bind)
void EffectDirPath::cleanup(std::string path) {
  bool _x = [&]() -> bool {
    std::error_code _ec;
    std::filesystem::remove_all(std::filesystem::path(path), _ec);
    return !_ec;
  }();
  std::cout << "cleaned up"s << '\n';
  return;
}
