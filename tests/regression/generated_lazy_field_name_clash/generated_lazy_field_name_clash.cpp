#include "generated_lazy_field_name_clash.h"

GeneratedLazyFieldNameClash::d_lazyV_
GeneratedLazyFieldNameClash::true_stream() {
  return d_lazyV_::lazy_([]() -> GeneratedLazyFieldNameClash::d_lazyV_ {
    return d_lazyV_::cons(true, true_stream());
  });
}

bool GeneratedLazyFieldNameClash::head(
    GeneratedLazyFieldNameClash::d_lazyV_ s) {
  const auto &[d_a0, d_a1] =
      std::get<typename GeneratedLazyFieldNameClash::d_lazyV_::Cons>(s.v());
  return d_a0;
}
