#include <string_literal_trigraph.h>

#include <iostream>
#include <string>

int main() {
  std::string m = StringLiteralTrigraph::marks;
  std::cout << m.size() << std::endl;
  return (m.size() == 3 && m[0] == '?' && m[1] == '?' && m[2] == '=') ? 0 : 1;
}
