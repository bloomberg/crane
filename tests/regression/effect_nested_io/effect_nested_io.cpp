#include <effect_nested_io.h>

/// 1. Block template result used inside constructor (Some)
std::optional<std::string> EffectNestedIo::read_optional() {
  std::string line;
  std::getline(std::cin, line);
  return std::make_optional<std::string>(line);
}

/// 2. Block template result used in a pair
std::pair<std::string, int64_t> EffectNestedIo::read_pair() {
  std::string line;
  std::getline(std::cin, line);
  int64_t len = line.length();
  return std::make_pair(line, len);
}

/// 3. Block template result concatenated with another string
std::string EffectNestedIo::read_and_greet() {
  std::string name;
  std::getline(std::cin, name);
  std::string greeting = "Hello, "s + name;
  return greeting;
}

/// 4. Two block templates, results used in pair
std::pair<std::string, std::string> EffectNestedIo::read_two_lines() {
  std::string a;
  std::getline(std::cin, a);
  std::string b;
  std::getline(std::cin, b);
  return std::make_pair(a, b);
}

/// 5. Block template in function that also uses clock effect
std::pair<std::string, int64_t> EffectNestedIo::timed_read() {
  int64_t _x = static_cast<int64_t>(
      std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::steady_clock::now().time_since_epoch())
          .count());
  std::string line;
  std::getline(std::cin, line);
  int64_t t2 = static_cast<int64_t>(
      std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::steady_clock::now().time_since_epoch())
          .count());
  return std::make_pair(line, t2);
}

/// 6. Block template result stored in env
std::string EffectNestedIo::read_and_store(const std::string key) {
  std::string line;
  std::getline(std::cin, line);
  setenv(key.c_str(), line.c_str(), 1);
  return line;
}

/// 7. Multiple block templates interleaved with env effects
std::pair<std::string, std::string> EffectNestedIo::multi_read_store() {
  std::string k;
  std::getline(std::cin, k);
  setenv("KEY"s.c_str(), k.c_str(), 1);
  std::string v;
  std::getline(std::cin, v);
  setenv("VALUE"s.c_str(), v.c_str(), 1);
  return std::make_pair(k, v);
}

/// 8. Block template result length checked
int64_t EffectNestedIo::read_length() {
  std::string line;
  std::getline(std::cin, line);
  return line.length();
}
