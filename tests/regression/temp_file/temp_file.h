#pragma once

#include <cerrno>
#include <fcntl.h>
#include <filesystem>
#include <random>
#include <stdexcept>
#include <string>
#include <string_view>
#include <sys/stat.h>
#include <unistd.h>

struct TempFile {
  static std::string make_temp_file(const std::string &prefix);
  static std::string make_temp_dir(const std::string &prefix);
};
