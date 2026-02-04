#include <algorithm>
#include <any>
#include <args.h>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

unsigned int Args::f(const std::shared_ptr<Args::R> &r, const unsigned int _x0,
                     const unsigned int _x1) {
  return r->f(_x0, _x1);
}

unsigned int Args::_tag(const std::shared_ptr<Args::R> &r) { return r->_tag; }

unsigned int Args::apply_record(const std::shared_ptr<Args::R> &r,
                                const unsigned int a, const unsigned int b) {
  return r->f(a, b);
}
