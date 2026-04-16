#ifndef INCLUDED_TEMP_FILE
#define INCLUDED_TEMP_FILE

#include <cstdlib>
#include <filesystem>
#include <string>
#include <type_traits>
#include <unistd.h>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct TempFile {
  static std::string make_temp_file(const std::string prefix);
  static std::string make_temp_dir(const std::string prefix);
};

#endif // INCLUDED_TEMP_FILE
