#include <bank_lookup_default.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<BankLookupDefault::ram_bank>
BankLookupDefault::get_bank(const std::shared_ptr<BankLookupDefault::state> &s,
                            const unsigned int b) {
  return s->ram_sys->nth(b, empty_bank);
}
