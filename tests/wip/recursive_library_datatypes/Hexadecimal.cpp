#include "Hexadecimal.h"

#include "Datatypes.h"
#include "Decimal.h"
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
  } else if (std::holds_alternative<typename uint::D9>(d.v())) {
    const auto &[a0] = std::get<typename uint::D9>(d.v());
    return uint::da(*a0);
  } else if (std::holds_alternative<typename uint::Da>(d.v())) {
    const auto &[a0] = std::get<typename uint::Da>(d.v());
    return uint::db(*a0);
  } else if (std::holds_alternative<typename uint::Db>(d.v())) {
    const auto &[a0] = std::get<typename uint::Db>(d.v());
    return uint::dc(*a0);
  } else if (std::holds_alternative<typename uint::Dc>(d.v())) {
    const auto &[a0] = std::get<typename uint::Dc>(d.v());
    return uint::dd(*a0);
  } else if (std::holds_alternative<typename uint::Dd>(d.v())) {
    const auto &[a0] = std::get<typename uint::Dd>(d.v());
    return uint::de(*a0);
  } else if (std::holds_alternative<typename uint::De>(d.v())) {
    const auto &[a0] = std::get<typename uint::De>(d.v());
    return uint::df(*a0);
  } else {
    const auto &[a0] = std::get<typename uint::Df>(d.v());
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
    return uint::da(double_(*a0));
  } else if (std::holds_alternative<typename uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename uint::D6>(d.v());
    return uint::dc(double_(*a0));
  } else if (std::holds_alternative<typename uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename uint::D7>(d.v());
    return uint::de(double_(*a0));
  } else if (std::holds_alternative<typename uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename uint::D8>(d.v());
    return uint::d0(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::D9>(d.v())) {
    const auto &[a0] = std::get<typename uint::D9>(d.v());
    return uint::d2(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::Da>(d.v())) {
    const auto &[a0] = std::get<typename uint::Da>(d.v());
    return uint::d4(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::Db>(d.v())) {
    const auto &[a0] = std::get<typename uint::Db>(d.v());
    return uint::d6(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::Dc>(d.v())) {
    const auto &[a0] = std::get<typename uint::Dc>(d.v());
    return uint::d8(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::Dd>(d.v())) {
    const auto &[a0] = std::get<typename uint::Dd>(d.v());
    return uint::da(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::De>(d.v())) {
    const auto &[a0] = std::get<typename uint::De>(d.v());
    return uint::dc(succ_double(*a0));
  } else {
    const auto &[a0] = std::get<typename uint::Df>(d.v());
    return uint::de(succ_double(*a0));
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
    return uint::db(double_(*a0));
  } else if (std::holds_alternative<typename uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename uint::D6>(d.v());
    return uint::dd(double_(*a0));
  } else if (std::holds_alternative<typename uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename uint::D7>(d.v());
    return uint::df(double_(*a0));
  } else if (std::holds_alternative<typename uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename uint::D8>(d.v());
    return uint::d1(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::D9>(d.v())) {
    const auto &[a0] = std::get<typename uint::D9>(d.v());
    return uint::d3(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::Da>(d.v())) {
    const auto &[a0] = std::get<typename uint::Da>(d.v());
    return uint::d5(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::Db>(d.v())) {
    const auto &[a0] = std::get<typename uint::Db>(d.v());
    return uint::d7(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::Dc>(d.v())) {
    const auto &[a0] = std::get<typename uint::Dc>(d.v());
    return uint::d9(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::Dd>(d.v())) {
    const auto &[a0] = std::get<typename uint::Dd>(d.v());
    return uint::db(succ_double(*a0));
  } else if (std::holds_alternative<typename uint::De>(d.v())) {
    const auto &[a0] = std::get<typename uint::De>(d.v());
    return uint::dd(succ_double(*a0));
  } else {
    const auto &[a0] = std::get<typename uint::Df>(d.v());
    return uint::df(succ_double(*a0));
  }
}
