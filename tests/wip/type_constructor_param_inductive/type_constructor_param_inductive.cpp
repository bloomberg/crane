#include "type_constructor_param_inductive.h"

uint64_t TypeConstructorParamInductive::size_list(
    const TypeConstructorParamInductive::wrapped<List, uint64_t> &w) {
  if (std::holds_alternative<typename TypeConstructorParamInductive::wrapped<
          List<std::any>, uint64_t>::Wrap>(w.v())) {
    const auto &[a0] = std::get<typename TypeConstructorParamInductive::wrapped<
        List<std::any>, uint64_t>::Wrap>(w.v());
    return a0.length();
  } else {
    const auto &[a0, a1] =
        std::get<typename TypeConstructorParamInductive::wrapped<
            List<std::any>, uint64_t>::Pair2>(w.v());
    return (a0.length() + a1.length());
  }
}

uint64_t TypeConstructorParamInductive::size_opt(
    const TypeConstructorParamInductive::wrapped<std::optional, uint64_t> &w) {
  if (std::holds_alternative<typename TypeConstructorParamInductive::wrapped<
          std::optional<std::any>, uint64_t>::Wrap>(w.v())) {
    const auto &[a0] = std::get<typename TypeConstructorParamInductive::wrapped<
        std::optional<std::any>, uint64_t>::Wrap>(w.v());
    if (a0.has_value()) {
      const uint64_t &_x = *a0;
      return UINT64_C(1);
    } else {
      return UINT64_C(0);
    }
  } else {
    const auto &[a0, a1] =
        std::get<typename TypeConstructorParamInductive::wrapped<
            std::optional<std::any>, uint64_t>::Pair2>(w.v());
    return ([&]() -> uint64_t {
      if (a0.has_value()) {
        const uint64_t &_x = *a0;
        return UINT64_C(1);
      } else {
        return UINT64_C(0);
      }
    }() + [&]() -> uint64_t {
      if (a1.has_value()) {
        const uint64_t &_x = *a1;
        return UINT64_C(1);
      } else {
        return UINT64_C(0);
      }
    }());
  }
}
