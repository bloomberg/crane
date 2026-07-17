#include "temp_file.h"

std::string TempFile::make_temp_file(std::string prefix) {
  return [&]() -> std::string {
    std::string _n = std::filesystem::path(prefix).filename().string();
    if (_n.empty() || _n == "." || _n == "..")
      _n = "tmp";
    std::filesystem::path _base = std::filesystem::temp_directory_path();
    std::random_device _rng;
    for (;;) {
      std::string _d =
          (_base / (_n + std::to_string(_rng()) + std::to_string(_rng())))
              .string();
      if (::mkdir(_d.c_str(), 0700) != 0) {
        if (errno == EEXIST)
          continue;
        throw std::runtime_error("crane: failed to create temporary directory");
      }
      std::string _p = _d + "/" + _n;
      int _fd = ::open(_p.c_str(), O_CREAT | O_EXCL | O_RDWR, 0600);
      if (_fd < 0)
        throw std::runtime_error("crane: failed to create temporary file");
      ::close(_fd);
      return _p;
    }
  }();
}

std::string TempFile::make_temp_dir(std::string prefix) {
  return [&]() -> std::string {
    std::string _n = std::filesystem::path(prefix).filename().string();
    if (_n.empty() || _n == "." || _n == "..")
      _n = "tmp";
    std::filesystem::path _dir = std::filesystem::temp_directory_path();
    std::random_device _rng;
    for (;;) {
      std::string _p =
          (_dir / (_n + std::to_string(_rng()) + std::to_string(_rng())))
              .string();
      if (::mkdir(_p.c_str(), 0700) == 0)
        return _p;
      if (errno != EEXIST)
        throw std::runtime_error("crane: failed to create temporary directory");
    }
  }();
}
