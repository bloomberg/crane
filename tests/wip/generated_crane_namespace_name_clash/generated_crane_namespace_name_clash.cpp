#include <generated_crane_namespace_name_clash.h>

crane::stream crane::ones() {
  return stream::lazy_(
      []() -> crane::stream { return stream::cons(true, ones()); });
}

bool crane::head(const crane::stream s) {
  const auto &[d_a0, d_a1] = std::get<typename crane::stream::Cons>(s.v());
  return d_a0;
}
