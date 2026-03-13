#include <wrm_then_rdm_reads_back.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int WrmThenRdmReadsBack::get_reg(
    const std::shared_ptr<WrmThenRdmReadsBack::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0u);
}

__attribute__((pure)) unsigned int WrmThenRdmReadsBack::get_reg_pair(
    const std::shared_ptr<WrmThenRdmReadsBack::state> &s,
    const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<WrmThenRdmReadsBack::state>
WrmThenRdmReadsBack::execute_src(std::shared_ptr<WrmThenRdmReadsBack::state> s,
                                 const unsigned int r) {
  return std::make_shared<WrmThenRdmReadsBack::state>(
      state{s->regs, s->acc, s->ram, (get_reg_pair(s, std::move(r)) % 16u)});
}

std::shared_ptr<WrmThenRdmReadsBack::state> WrmThenRdmReadsBack::execute_wrm(
    std::shared_ptr<WrmThenRdmReadsBack::state> s) {
  return std::make_shared<WrmThenRdmReadsBack::state>(state{
      s->regs, s->acc, update_nth<unsigned int>(s->sel_char, s->acc, s->ram),
      s->sel_char});
}

std::shared_ptr<WrmThenRdmReadsBack::state> WrmThenRdmReadsBack::execute_rdm(
    std::shared_ptr<WrmThenRdmReadsBack::state> s) {
  return std::make_shared<WrmThenRdmReadsBack::state>(
      state{s->regs, s->ram->nth(s->sel_char, 0u), s->ram, s->sel_char});
}
