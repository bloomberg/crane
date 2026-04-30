#include <wrm_then_rdm_reads_back.h>

unsigned int WrmThenRdmReadsBack::get_reg(const WrmThenRdmReadsBack::state &s,
                                          const unsigned int &r) {
  return ListDef::template nth<unsigned int>(r, s.regs, 0u);
}

unsigned int
WrmThenRdmReadsBack::get_reg_pair(const WrmThenRdmReadsBack::state &s,
                                  const unsigned int &r) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

WrmThenRdmReadsBack::state
WrmThenRdmReadsBack::execute_src(const WrmThenRdmReadsBack::state &s,
                                 const unsigned int &r) {
  return state{s.regs, s.acc, s.ram,
               (16u ? get_reg_pair(s, r) % 16u : get_reg_pair(s, r))};
}

WrmThenRdmReadsBack::state
WrmThenRdmReadsBack::execute_wrm(const WrmThenRdmReadsBack::state &s) {
  return state{s.regs, s.acc,
               update_nth<unsigned int>(s.sel_char, s.acc, s.ram), s.sel_char};
}

WrmThenRdmReadsBack::state
WrmThenRdmReadsBack::execute_rdm(const WrmThenRdmReadsBack::state &s) {
  return state{s.regs,
               ListDef::template nth<unsigned int>(s.sel_char, s.ram, 0u),
               s.ram, s.sel_char};
}
