#pragma once

#include <cerrno>
#include <fcntl.h>
#include <filesystem>
#include <random>
#include <stdexcept>
#include <string>
#include <sys/stat.h>
#include <unistd.h>
#include <utility>

struct TempFile {
  static std::string make_temp_file(std::string prefix);
  static std::string make_temp_dir(std::string prefix);
};
