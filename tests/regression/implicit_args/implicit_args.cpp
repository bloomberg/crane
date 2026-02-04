#include <algorithm>
#include <any>
#include <functional>
#include <implicit_args.h>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

unsigned int ImplicitArgs::add_one(const unsigned int _x0) {
  return [](const unsigned int _x0) { return (1u + _x0); }(_x0);
}

unsigned int ImplicitArgs::double_nat(const unsigned int n) { return (n + n); }
