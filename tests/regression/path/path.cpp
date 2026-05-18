#include "path.h"

std::string Path::abs_path(std::string p) {
  return std::filesystem::absolute(std::filesystem::path(p)).string();
}

std::string Path::canon_path(std::string p) {
  return std::filesystem::canonical(std::filesystem::path(p)).string();
}

std::string Path::rel_path(std::string p) {
  return std::filesystem::relative(std::filesystem::path(p)).string();
}

bool Path::check_is_dir(std::string p) {
  return std::filesystem::is_directory(std::filesystem::path(p));
}

bool Path::check_is_file(std::string p) {
  return std::filesystem::is_regular_file(std::filesystem::path(p));
}
