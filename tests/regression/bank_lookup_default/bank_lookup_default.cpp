#include <bank_lookup_default.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<BankLookupDefault::ram_bank>
BankLookupDefault::get_bank(const std::shared_ptr<BankLookupDefault::state> &s,
                            const unsigned int b) {
  return ListDef::template nth<std::shared_ptr<BankLookupDefault::ram_bank>>(
      b, s->ram_sys, empty_bank);
}
