#ifndef INCLUDED_EFFECT_WORKFLOW
#define INCLUDED_EFFECT_WORKFLOW

#include <cerrno>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fcntl.h>
#include <filesystem>
#include <iostream>
#include <memory>
#include <optional>
#include <random>
#include <stdexcept>
#include <string>
#include <sys/stat.h>
#include <system_error>
#include <unistd.h>
#include <utility>
#include <variant>

using namespace std::string_literals;

struct EffectWorkflow {
  static std::string full_workflow(std::string prefix);
  static std::string conditional_create(std::string path);
  static void read_and_set();
  static uint64_t repeat_log(uint64_t n, std::string msg);
  static std::string env_or_create(std::string name, std::string path);
  static int64_t read_length();
  static std::pair<std::string, std::string> double_read();
  static int64_t return_literal();
};

#endif // INCLUDED_EFFECT_WORKFLOW
