#include "block_template_stress.h"

List<std::string> BlockTemplateStress::read_n_lines(uint64_t n) {
  if (n <= 0) {
    return List<std::string>::nil();
  } else {
    uint64_t n_ = n - 1;
    std::string line;
    std::getline(std::cin, line);
    List<std::string> rest = read_n_lines(n_);
    return List<std::string>::cons(line, rest);
  }
}

std::string BlockTemplateStress::conditional_read(bool do_read) {
  if (do_read) {
    std::string s;
    std::getline(std::cin, s);
    return s + "!"s;
  } else {
    return "skipped";
  }
}

uint64_t BlockTemplateStress::read_and_add() {
  uint64_t n;
  std::cin >> n;
  return (n + UINT64_C(1));
}

std::string BlockTemplateStress::branch_read(uint64_t choice) {
  if (choice <= 0) {
    std::string a;
    std::getline(std::cin, a);
    return "zero: "s + a;
  } else {
    uint64_t n = choice - 1;
    if (n <= 0) {
      std::string b;
      std::getline(std::cin, b);
      return "one: "s + b;
    } else {
      uint64_t _x = n - 1;
      std::string c;
      std::getline(std::cin, c);
      return "other: "s + c;
    }
  }
}

uint64_t BlockTemplateStress::read_two_nats() {
  uint64_t a;
  std::cin >> a;
  uint64_t b;
  std::cin >> b;
  return (a + b);
}

void BlockTemplateStress::block_result_as_arg() {
  uint64_t _x;
  std::cin >> _x;
  std::string s;
  std::getline(std::cin, s);
  std::cout << s + " read"s << '\n';
  return;
}

List<std::string>
BlockTemplateStress::read_files(const List<std::string> &paths) {
  if (std::holds_alternative<typename List<std::string>::Nil>(paths.v())) {
    return List<std::string>::nil();
  } else {
    const auto &[a0, a1] =
        std::get<typename List<std::string>::Cons>(paths.v());
    std::string content;
    {
      std::ifstream _f(a0);
      if (_f.good())
        std::getline(_f, content);
      else
        content = a0;
    };
    List<std::string> rest = read_files(*a1);
    return List<std::string>::cons(content, rest);
  }
}

std::string BlockTemplateStress::interleaved_void() {
  std::cout << "Enter name:"s << '\n';
  std::string name;
  std::getline(std::cin, name);
  std::cout << "Hello, "s + name << '\n';
  std::cout << "Enter age:"s << '\n';
  std::string age;
  std::getline(std::cin, age);
  return name + " is "s + age;
}
