#include "block_template_hygiene.h"

std::string BlockTemplateHygiene::same_name_twice() {
  std::string _x;
  std::getline(std::cin, _x);
  std::string s;
  std::getline(std::cin, s);
  return s + " (second)"s;
}

std::string BlockTemplateHygiene::same_name_thrice() {
  std::string _x;
  std::getline(std::cin, _x);
  std::string _x0;
  std::getline(std::cin, _x0);
  std::string s;
  std::getline(std::cin, s);
  return s + " (third)"s;
}

std::string BlockTemplateHygiene::shadow_internal_name() {
  std::string s;
  std::getline(std::cin, s);
  return s + "!"s;
}

std::string BlockTemplateHygiene::interleaved_templates() {
  std::string a;
  std::getline(std::cin, a);
  std::cout << a;
  std::string b;
  std::getline(std::cin, b);
  std::cout << b << '\n';
  std::string c;
  std::getline(std::cin, c);
  return a + b + c;
}

std::string BlockTemplateHygiene::block_with_args() {
  std::string s;
  {
    std::ifstream _f("data.txt"s);
    std::getline(_f, s);
  };
  return s + " read"s;
}

std::string BlockTemplateHygiene::block_with_args_same_name() {
  std::string _x;
  {
    std::ifstream _f("a.txt"s);
    std::getline(_f, _x);
  };
  std::string s;
  {
    std::ifstream _f("b.txt"s);
    std::getline(_f, s);
  };
  return s + " done"s;
}

void BlockTemplateHygiene::result_in_expr() {
  std::string name;
  std::getline(std::cin, name);
  std::cout << "Hello, "s + name << '\n';
  return;
}

std::string BlockTemplateHygiene::let_after_block() {
  std::string first;
  std::getline(std::cin, first);
  std::string last;
  std::getline(std::cin, last);
  std::string full = std::move(first) + " "s + std::move(last);
  return full;
}

std::string BlockTemplateHygiene::bind_named_result() {
  std::string result;
  std::getline(std::cin, result);
  return result + "!"s;
}

std::string BlockTemplateHygiene::bind_named_underscore_r() {
  std::string _r;
  std::getline(std::cin, _r);
  return _r + "!"s;
}

std::string BlockTemplateHygiene::expr_position_iife() {
  return []() -> std::string {
    std::string _r;
    std::getline(std::cin, _r);
    return _r;
  }();
}
