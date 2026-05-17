#include "bank_lookup_default.h"

BankLookupDefault::ram_bank
BankLookupDefault::get_bank(const BankLookupDefault::state &s, uint64_t b) {
  return ListDef::template nth<BankLookupDefault::ram_bank>(b, s.ram_sys,
                                                            empty_bank);
}
