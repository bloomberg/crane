#include "generated_variant_alias_name_clash.h"

bool GeneratedVariantAliasNameClash::is_flag(
    const GeneratedVariantAliasNameClash::variant_t0 &x) {
  if (std::holds_alternative<
          typename GeneratedVariantAliasNameClash::variant_t0::Empty>(x.v())) {
    return false;
  } else {
    const auto &[a0] =
        std::get<typename GeneratedVariantAliasNameClash::variant_t0::Flag>(
            x.v());
    return a0;
  }
}
