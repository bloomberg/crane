#include "wrm_then_rdm_reads_back.h"

uint64_t WrmThenRdmReadsBack::get_reg(const WrmThenRdmReadsBack::state &s,
                                      uint64_t r) {
  return ListDef::template nth<uint64_t>(r, s.regs, UINT64_C(0));
}

uint64_t WrmThenRdmReadsBack::get_reg_pair(const WrmThenRdmReadsBack::state &s,
                                           uint64_t r) {
  uint64_t base = (((r - (UINT64_C(2) ? r % UINT64_C(2) : r)) > r
                        ? 0
                        : (r - (UINT64_C(2) ? r % UINT64_C(2) : r))));
  return ((get_reg(s, base) * UINT64_C(16)) + get_reg(s, (base + UINT64_C(1))));
}

WrmThenRdmReadsBack::state
WrmThenRdmReadsBack::execute_src(const WrmThenRdmReadsBack::state &s,
                                 uint64_t r) {
  return state{
      s.regs, s.acc, s.ram,
      (UINT64_C(16) ? get_reg_pair(s, r) % UINT64_C(16) : get_reg_pair(s, r))};
}

WrmThenRdmReadsBack::state
WrmThenRdmReadsBack::execute_wrm(const WrmThenRdmReadsBack::state &s) {
  return state{s.regs, s.acc, update_nth<uint64_t>(s.sel_char, s.acc, s.ram),
               s.sel_char};
}

WrmThenRdmReadsBack::state
WrmThenRdmReadsBack::execute_rdm(const WrmThenRdmReadsBack::state &s) {
  return state{s.regs,
               ListDef::template nth<uint64_t>(s.sel_char, s.ram, UINT64_C(0)),
               s.ram, s.sel_char};
}
