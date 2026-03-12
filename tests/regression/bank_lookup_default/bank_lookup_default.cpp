#include <bank_lookup_default.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<BankLookupDefault::ram_bank>
BankLookupDefault::get_bank(const std::shared_ptr<BankLookupDefault::state> &s,
                            const unsigned int b) {
  return s->ram_sys->nth(b, empty_bank);
}
