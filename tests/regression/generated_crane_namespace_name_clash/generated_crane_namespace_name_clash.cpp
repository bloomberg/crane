#include "generated_crane_namespace_name_clash.h"

crane_::stream crane_::ones() {
  return stream::lazy_(
      []() -> typename crane_::stream::Cons { return {true, ones()}; });
}

bool crane_::head(const crane_::stream &s) {
  const auto &[a0, a1] = std::get<typename crane_::stream::Cons>(s.v());
  return a0;
}
