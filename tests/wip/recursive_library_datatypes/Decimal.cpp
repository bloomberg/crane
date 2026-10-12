#include "Decimal.h"

#include "Datatypes.h"
#include "Specif.h"

uint Little::succ(const uint &d) {
  if (std::holds_alternative<typename uint::Nil>(d.v())) {
    return uint::d1(uint::nil());
  } else if (std::holds_alternative<typename uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename uint::D0>(d.v());
    return uint::d1(*a0);
  } else if (std::holds_alternative<typename uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename uint::D1>(d.v());
    return uint::d2(*a0);
  } else if (std::holds_alternative<typename uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename uint::D2>(d.v());
    return uint::d3(*a0);
  } else if (std::holds_alternative<typename uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename uint::D3>(d.v());
    return uint::d4(*a0);
  } else if (std::holds_alternative<typename uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename uint::D4>(d.v());
    return uint::d5(*a0);
  } else if (std::holds_alternative<typename uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename uint::D5>(d.v());
    return uint::d6(*a0);
  } else if (std::holds_alternative<typename uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename uint::D6>(d.v());
    return uint::d7(*a0);
  } else if (std::holds_alternative<typename uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename uint::D7>(d.v());
    return uint::d8(*a0);
  } else if (std::holds_alternative<typename uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename uint::D8>(d.v());
    return uint::d9(*a0);
  } else {
    const auto &[a0] = std::get<typename uint::D9>(d.v());
    return uint::d0(succ(*a0));
  }
}

uint Little::double_(const uint &d) {
  if (std::holds_alternative<typename uint::Nil>(d.v())) {
    return uint::nil();
  } else if (std::holds_alternative<typename uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename uint::D0>(d.v());
    return uint::d0(double_(*a0));
  } else if (std::holds_alternative<typename uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename uint::D1>(d.v());
    return uint::d2(double_(*a0));
  } else if (std::holds_alternative<typename uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename uint::D2>(d.v());
    return uint::d4(double_(*a0));
  } else if (std::holds_alternative<typename uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename uint::D3>(d.v());
    return uint::d6(double_(*a0));
  } else if (std::holds_alternative<typename uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename uint::D4>(d.v());
    return uint::d8(double_(*a0));
  } else if (std::holds_alternative<typename uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename uint::D5>(d.v());
    return uint::d0(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename uint::D6>(d.v());
    return uint::d2(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename uint::D7>(d.v());
    return uint::d4(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename uint::D8>(d.v());
    return uint::d6(succ_double(*a0));
  } else {
    const auto &[a0] = std::get<typename uint::D9>(d.v());
    return uint::d8(succ_double(*a0));
  }
}

uint Little::succ_double(const uint &d) {
  if (std::holds_alternative<typename uint::Nil>(d.v())) {
    return uint::d1(uint::nil());
  } else if (std::holds_alternative<typename uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename uint::D0>(d.v());
    return uint::d1(double_(*a0));
  } else if (std::holds_alternative<typename uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename uint::D1>(d.v());
    return uint::d3(double_(*a0));
  } else if (std::holds_alternative<typename uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename uint::D2>(d.v());
    return uint::d5(double_(*a0));
  } else if (std::holds_alternative<typename uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename uint::D3>(d.v());
    return uint::d7(double_(*a0));
  } else if (std::holds_alternative<typename uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename uint::D4>(d.v());
    return uint::d9(double_(*a0));
  } else if (std::holds_alternative<typename uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename uint::D5>(d.v());
    return uint::d1(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename uint::D6>(d.v());
    return uint::d3(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename uint::D7>(d.v());
    return uint::d5(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename uint::D8>(d.v());
    return uint::d7(succ_double(*a0));
  } else {
    const auto &[a0] = std::get<typename uint::D9>(d.v());
    return uint::d9(succ_double(*a0));
  }
}
