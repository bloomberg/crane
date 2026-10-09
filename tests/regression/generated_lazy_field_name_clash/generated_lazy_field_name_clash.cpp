#include "generated_lazy_field_name_clash.h"

GeneratedLazyFieldNameClash::d_lazyV_
GeneratedLazyFieldNameClash::true_stream() {
  return d_lazyV_::lazy_([]() ->
                         typename GeneratedLazyFieldNameClash::d_lazyV_::Cons {
                           return {true, true_stream()};
                         });
}

bool GeneratedLazyFieldNameClash::head(
    const GeneratedLazyFieldNameClash::d_lazyV_ &s) {
  const auto &[a0, a1] =
      std::get<typename GeneratedLazyFieldNameClash::d_lazyV_::Cons>(s.v());
  return a0;
}
