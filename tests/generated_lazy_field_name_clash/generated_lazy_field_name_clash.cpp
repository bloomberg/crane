#include "generated_lazy_field_name_clash.h"

GeneratedLazyFieldNameClash::d_lazyV_
GeneratedLazyFieldNameClash::true_stream() {
  return d_lazyV_::lazy_([]() -> GeneratedLazyFieldNameClash::d_lazyV_ {
    return d_lazyV_::cons(true, true_stream());
  });
}

bool GeneratedLazyFieldNameClash::head(
    GeneratedLazyFieldNameClash::d_lazyV_ s) {
  const auto &[a0, a1] =
      std::get<typename GeneratedLazyFieldNameClash::d_lazyV_::Cons>(s.v());
  return a0;
}
