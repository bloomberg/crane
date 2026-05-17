#ifndef INCLUDED_BIND_ETA_REDUCED
#define INCLUDED_BIND_ETA_REDUCED

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <type_traits>

struct BindEtaReduced {
  /// Bug case 1: bind with a callback as continuation.
  /// get_line is bound, then f is applied to the result.
  /// Coq reduces fun line => f line to f, breaking the bind.
  template <typename F0> static std::string with_line(F0 &&f) {
    std::string _bind_result = []() -> std::string {
      std::string _r;
      std::getline(std::cin, _r);
      return _r;
    }();
    return f(_bind_result);
  }

  /// Bug case 2: same with a pure callback.
  template <typename F0>
    requires std::is_invocable_r_v<std::string, F0 &, std::string &>
  static std::string transform(F0 &&f) {
    std::string line;
    std::getline(std::cin, line);
    return f(line);
  }

  /// Control case: explicit lambda prevents eta-reduction.
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
