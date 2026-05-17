#ifndef INCLUDED_TEMP_FILE
#define INCLUDED_TEMP_FILE

#include <cstdlib>
#include <filesystem>
#include <string>
#include <unistd.h>

struct TempFile {
  static std::string make_temp_file(std::string prefix);
  static std::string make_temp_dir(std::string prefix);
};

#endif // INCLUDED_TEMP_FILE
