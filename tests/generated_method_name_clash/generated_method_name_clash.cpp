#include "generated_method_name_clash.h"

bool GeneratedMethodNameClash::is_clone(
    const GeneratedMethodNameClash::token &t) {
  if (std::holds_alternative<typename GeneratedMethodNameClash::token::Clone>(
          t.v())) {
    return true;
  } else if (std::holds_alternative<
                 typename GeneratedMethodNameClash::token::V>(t.v())) {
    return false;
  } else {
    const auto &[a0] =
        std::get<typename GeneratedMethodNameClash::token::Other>(t.v());
    return a0;
  }
}
