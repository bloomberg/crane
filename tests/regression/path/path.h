#ifndef INCLUDED_PATH
#define INCLUDED_PATH

#include <filesystem>
#include <string>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Path {
  static std::string abs_path(const std::string p);
  static std::string canon_path(const std::string p);
  static std::string rel_path(const std::string p);
  static bool check_is_dir(const std::string p);
  static bool check_is_file(const std::string p);
};

#endif // INCLUDED_PATH
