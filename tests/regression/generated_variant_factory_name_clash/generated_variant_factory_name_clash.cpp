#include "generated_variant_factory_name_clash.h"

bool GeneratedVariantFactoryNameClash::is_variant(
    const GeneratedVariantFactoryNameClash::token &t) {
  if (std::holds_alternative<
          typename GeneratedVariantFactoryNameClash::token::Variant_t>(t.v())) {
    return true;
  } else {
    const auto &[d_a0] =
        std::get<typename GeneratedVariantFactoryNameClash::token::Other>(
            t.v());
    return d_a0;
  }
}
