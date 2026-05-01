#include <generated_crane_namespace_name_clash.h>

crane_::stream crane_::ones() {
  return stream::lazy_(
      []() -> crane_::stream { return stream::cons(true, ones()); });
}

bool crane_::head(const crane_::stream s) {
  const auto &[d_a0, d_a1] = std::get<typename crane_::stream::Cons>(s.v());
  return d_a0;
}
