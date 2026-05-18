#ifndef INCLUDED_PATH
#define INCLUDED_PATH

#include <filesystem>
#include <string>

struct Path {
  static std::string abs_path(std::string p);
  static std::string canon_path(std::string p);
  static std::string rel_path(std::string p);
  static bool check_is_dir(std::string p);
  static bool check_is_file(std::string p);
};

#endif // INCLUDED_PATH
