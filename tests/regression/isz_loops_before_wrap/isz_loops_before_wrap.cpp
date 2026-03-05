#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <isz_loops_before_wrap.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
IszLoopsBeforeWrap::regs(const std::shared_ptr<IszLoopsBeforeWrap::state> &s) {
  return s->regs;
}

unsigned int
IszLoopsBeforeWrap::get_reg(const std::shared_ptr<IszLoopsBeforeWrap::state> &s,
                            const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int IszLoopsBeforeWrap::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

bool IszLoopsBeforeWrap::isz_loops(
    const std::shared_ptr<IszLoopsBeforeWrap::state> &s, const unsigned int r) {
  return !((nibble_of_nat((get_reg(s, r) + (0 + 1))) == 0));
}
