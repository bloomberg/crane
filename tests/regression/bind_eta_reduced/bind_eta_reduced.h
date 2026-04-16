#ifndef INCLUDED_BIND_ETA_REDUCED
#define INCLUDED_BIND_ETA_REDUCED

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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
  template <MapsTo<std::string, std::string> F0>
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
