#ifndef INCLUDED_BLOCK_TEMPLATE_HYGIENE
#define INCLUDED_BLOCK_TEMPLATE_HYGIENE

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <system_error>
#include <utility>
#include <variant>

using namespace std::string_literals;

struct BlockTemplateHygiene {
  static std::string same_name_twice();
  static std::string same_name_thrice();
  static std::string shadow_internal_name();
  static std::string interleaved_templates();
  static std::string block_with_args();
  static std::string block_with_args_same_name();
  static void result_in_expr();
  static std::string let_after_block();
  static std::string bind_named_result();
  static std::string bind_named_underscore_r();
  static std::string expr_position_iife();
};

#endif // INCLUDED_BLOCK_TEMPLATE_HYGIENE
