#include "bde_loop_acc_fn_std_string.h"

#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_optional.h>
#include <bsl_stdexcept.h>
#include <bsl_string.h>
#include <bsl_string_view.h>
#include <bsl_type_traits.h>
#include <bsl_variant.h>
#include <bsl_vector.h>

namespace BloombergLP {}

bsl::optional<crane::fn<bsl::string(unsigned int)>>
BdeLoopAccFnStdString::last_fn(
    bool b, const List<unsigned int> &l,
    bsl::optional<crane::fn<bsl::string(unsigned int)>> z) {
  if (bsl::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return z;
  } else {
    const auto &[d_a0, d_a1] =
        bsl::get<typename List<unsigned int>::Cons>(l.v());
    const List<unsigned int> &d_a1_value = *d_a1;
    return last_fn(
        b, d_a1_value,
        (b ? bsl::make_optional<crane::fn<std::string(unsigned int)>>(
                 crane::fn<std::string(unsigned int)>(
                     [](unsigned int) { return bsl::string("a"); }))
           : z));
  }
}
