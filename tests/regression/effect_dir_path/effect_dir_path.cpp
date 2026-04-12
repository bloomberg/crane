#include <effect_dir_path.h>

#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// 1. list_directory result matched — exercises IIFE + list match
std::optional<std::string> EffectDirPath::first_file(const std::string path) {
  std::shared_ptr<List<std::string>> files =
      [&]() -> std::shared_ptr<List<std::string>> {
    auto result = List<std::string>::nil();
    for (const auto &entry : std::filesystem::directory_iterator(path)) {
      result = List<std::string>::cons(entry.path().filename().string(),
                                       std::move(result));
    }
    return result;
  }();
  return std::visit(Overloaded{[](const typename List<std::string>::Nil &)
                                   -> std::optional<std::string> {
                                 return std::optional<std::string>();
                               },
                               [](const typename List<std::string>::Cons &_args)
                                   -> std::optional<std::string> {
                                 return std::make_optional<std::string>(
                                     _args.d_a0);
                               }},
                    files->v());
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
unsigned int
EffectDirPath::count_entries(const std::shared_ptr<List<std::string>> &dirs,
                             const unsigned int acc) {
  return std::visit(
      Overloaded{
          [&](const typename List<std::string>::Nil &) -> unsigned int {
            return acc;
          },
          [&](const typename List<std::string>::Cons &_args) -> unsigned int {
            std::shared_ptr<List<std::string>> files =
                [&]() -> std::shared_ptr<List<std::string>> {
              auto result = List<std::string>::nil();
              for (const auto &entry :
                   std::filesystem::directory_iterator(_args.d_a0)) {
                result = List<std::string>::cons(
                    entry.path().filename().string(), std::move(result));
              }
              return result;
            }();
            unsigned int n = std::move(files)->length();
            return count_entries(_args.d_a1, (acc + n));
          }},
      dirs->v());
}

/// 8. remove_directory (returns bool but treated as unit in bind)
void EffectDirPath::cleanup(const std::string path) {
  bool _x = std::filesystem::remove_all(std::filesystem::path(path));
  std::cout << "cleaned up"s << '\n';
  return;
}
