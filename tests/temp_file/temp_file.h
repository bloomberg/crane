#ifndef INCLUDED_TEMP_FILE
#define INCLUDED_TEMP_FILE

#include <cerrno>
#include <fcntl.h>
#include <filesystem>
#include <random>
#include <stdexcept>
#include <string>
#include <sys/stat.h>
#include <unistd.h>

struct TempFile {
  static std::string make_temp_file(std::string prefix);
  static std::string make_temp_dir(std::string prefix);
};

#endif // INCLUDED_TEMP_FILE
