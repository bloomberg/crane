#ifndef INCLUDED_BIND_ETA_REDUCED
#define INCLUDED_BIND_ETA_REDUCED

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <system_error>
#include <type_traits>

struct BindEtaReduced {
  template <typename F0> static std::string with_line(F0 &&f) {
    std::string _bind_result = []() -> std::string {
      std::string _r;
      std::getline(std::cin, _r);
      return _r;
    }();
    return f(_bind_result);
  }

  template <typename F0>
    requires std::is_invocable_r_v<std::string, F0 &, std::string &>
  static std::string transform(F0 &&f) {
    std::string line;
    std::getline(std::cin, line);
    return f(line);
  }

  template <typename F0> static std::string with_line_explicit(F0 &&f) {
    std::string _bind_result = []() -> std::string {
      std::string _r;
      std::getline(std::cin, _r);
      return _r;
    }();
    return f(_bind_result);
  }
};

#endif // INCLUDED_BIND_ETA_REDUCED
