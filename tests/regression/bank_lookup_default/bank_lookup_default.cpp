#include <bank_lookup_default.h>

BankLookupDefault::ram_bank
BankLookupDefault::get_bank(const BankLookupDefault::state &s,
                            const unsigned int &b) {
  return ListDef::template nth<BankLookupDefault::ram_bank>(b, s.ram_sys,
                                                            empty_bank);
}
