#include "temp_file.h"

std::string TempFile::make_temp_file(std::string prefix) {
  return [&]() -> std::string {
    auto p = std::filesystem::temp_directory_path() / (prefix + "XXXXXX");
    std::string s = p.string();
    int fd = mkstemp(s.data());
    if (fd >= 0)
      ::close(fd);
    return s;
  }();
}

std::string TempFile::make_temp_dir(std::string prefix) {
  return [&]() -> std::string {
    auto p = std::filesystem::temp_directory_path() / (prefix + "XXXXXX");
    std::string s = p.string();
    return std::string(mkdtemp(s.data()));
  }();
}
