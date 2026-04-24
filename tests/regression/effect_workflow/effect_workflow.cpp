#include <effect_workflow.h>

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <unistd.h>
#include <utility>
#include <variant>

/// 1. Use 5 different effect types in one function
std::string EffectWorkflow::full_workflow(const std::string prefix) {
  int64_t _x = static_cast<int64_t>(
      std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::steady_clock::now().time_since_epoch())
          .count());
  std::string tmp = [&]() -> std::string {
    auto p = std::filesystem::temp_directory_path() / (prefix + "XXXXXX");
    std::string s = p.string();
    int fd = mkstemp(s.data());
    if (fd >= 0)
      ::close(fd);
    return s;
  }();
  bool _x0 = std::filesystem::create_directories(std::filesystem::path(tmp));
  setenv("LAST_TEMP"s.c_str(), tmp.c_str(), 1);
  std::cout << tmp << '\n';
  int64_t _x3 = static_cast<int64_t>(
      std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::steady_clock::now().time_since_epoch())
          .count());
  return tmp;
}

/// 2. Match on bool from create_directory inside a chain
std::string EffectWorkflow::conditional_create(const std::string path) {
  bool ok = std::filesystem::create_directories(std::filesystem::path(path));
  if (ok) {
    std::cout << "created"s << '\n';
    return path;
  } else {
    return "exists";
  }
}

/// 3. get_line (block template) followed by env set using the result
void EffectWorkflow::read_and_set() {
  std::string line;
  std::getline(std::cin, line);
  setenv("USER_INPUT"s.c_str(), line.c_str(), 1);
  return;
}

/// 4. Recursive function using effects
unsigned int EffectWorkflow::repeat_log(const unsigned int &n,
                                        const std::string msg) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    int64_t _x = static_cast<int64_t>(
        std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::steady_clock::now().time_since_epoch())
            .count());
    std::cout << msg << '\n';
    unsigned int r = repeat_log(n_, msg);
    return (r + 1);
  }
}

/// 5. Effect returning option, matched, then another effect
std::string EffectWorkflow::env_or_create(const std::string name,
                                          const std::string path) {
  std::optional<std::string> r = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  if (r.has_value()) {
    const std::string &v = *r;
    return v;
  } else {
    bool _x = std::filesystem::create_directories(std::filesystem::path(path));
    setenv(name.c_str(), path.c_str(), 1);
    return path;
  }
}

/// 6. Pure let after block template
int64_t EffectWorkflow::read_length() {
  std::string line;
  std::getline(std::cin, line);
  int64_t len = line.length();
  return len;
}

/// 7. Multiple block templates of different types
std::pair<std::string, std::string> EffectWorkflow::double_read() {
  std::string a;
  std::getline(std::cin, a);
  std::string b;
  std::getline(std::cin, b);
  return std::make_pair(a, b);
}

/// 8. Return int literal in monadic context
int64_t EffectWorkflow::return_literal() { return int64_t(42); }
