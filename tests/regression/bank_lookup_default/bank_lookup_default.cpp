#include <algorithm>
#include <any>
#include <bank_lookup_default.h>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int BankLookupDefault::chip_port(
    const std::shared_ptr<BankLookupDefault::ram_chip> &r) {
  return r->chip_port;
}

std::shared_ptr<List<std::shared_ptr<BankLookupDefault::ram_chip>>>
BankLookupDefault::bank_chips(
    const std::shared_ptr<BankLookupDefault::ram_bank> &r) {
  return r->bank_chips;
}

std::shared_ptr<List<std::shared_ptr<BankLookupDefault::ram_bank>>>
BankLookupDefault::ram_sys(const std::shared_ptr<BankLookupDefault::state> &s) {
  return s->ram_sys;
}

std::shared_ptr<BankLookupDefault::ram_bank>
BankLookupDefault::get_bank(const std::shared_ptr<BankLookupDefault::state> &s,
                            const unsigned int b) {
  return s->ram_sys->nth(b, empty_bank);
}
