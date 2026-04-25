#include <temp_file.h>

#include <cstdlib>
#include <filesystem>
#include <memory>
#include <string>
#include <type_traits>
#include <unistd.h>

std::string TempFile::make_temp_file(const std::string prefix) {
  return [&]() -> std::string {
    auto p = std::filesystem::temp_directory_path() / (prefix + "XXXXXX");
    std::string s = p.string();
    int fd = mkstemp(s.data());
    if (fd >= 0)
      ::close(fd);
    return s;
  }();
}

std::string TempFile::make_temp_dir(const std::string prefix) {
  return [&]() -> std::string {
    auto p = std::filesystem::temp_directory_path() / (prefix + "XXXXXX");
    std::string s = p.string();
    return std::string(mkdtemp(s.data()));
  }();
}
