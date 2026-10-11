#include "factory_hides_field_type.h"

uint64_t FactoryHidesFieldType::area(const FactoryHidesFieldType::shape &s) {
  if (std::holds_alternative<typename FactoryHidesFieldType::shape::Pt>(
          s.v())) {
    const auto &[a0] =
        std::get<typename FactoryHidesFieldType::shape::Pt>(s.v());
    return (a0.px * a0.py);
  } else {
    const auto &[a0] =
        std::get<typename FactoryHidesFieldType::shape::Tag>(s.v());
    return a0.px;
  }
}
