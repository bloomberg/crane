#include "Hexadecimal.h"

#include "Datatypes.h"
#include "Decimal.h"
#include "Specif.h"

namespace Hexadecimal {

Uint Little::succ(const Uint &d) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return Uint::d1(Uint::nil());
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return Uint::d1(*a0);
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return Uint::d2(*a0);
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return Uint::d3(*a0);
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return Uint::d4(*a0);
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return Uint::d5(*a0);
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return Uint::d6(*a0);
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return Uint::d7(*a0);
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return Uint::d8(*a0);
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return Uint::d9(*a0);
  } else if (std::holds_alternative<typename Uint::D9>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return Uint::da(*a0);
  } else if (std::holds_alternative<typename Uint::Da>(d.v())) {
    const auto &[a0] = std::get<typename Uint::Da>(d.v());
    return Uint::db(*a0);
  } else if (std::holds_alternative<typename Uint::Db>(d.v())) {
    const auto &[a0] = std::get<typename Uint::Db>(d.v());
    return Uint::dc(*a0);
  } else if (std::holds_alternative<typename Uint::Dc>(d.v())) {
    const auto &[a0] = std::get<typename Uint::Dc>(d.v());
    return Uint::dd(*a0);
  } else if (std::holds_alternative<typename Uint::Dd>(d.v())) {
    const auto &[a0] = std::get<typename Uint::Dd>(d.v());
    return Uint::de(*a0);
  } else if (std::holds_alternative<typename Uint::De>(d.v())) {
    const auto &[a0] = std::get<typename Uint::De>(d.v());
    return Uint::df(*a0);
  } else {
    const auto &[a0] = std::get<typename Uint::Df>(d.v());
    return Uint::d0(succ(*a0));
  }
}

Uint Little::double_(const Uint &d) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return Uint::nil();
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return Uint::d0(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return Uint::d2(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return Uint::d4(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return Uint::d6(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return Uint::d8(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return Uint::da(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return Uint::dc(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return Uint::de(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return Uint::d0(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::D9>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return Uint::d2(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::Da>(d.v())) {
    const auto &[a0] = std::get<typename Uint::Da>(d.v());
    return Uint::d4(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::Db>(d.v())) {
    const auto &[a0] = std::get<typename Uint::Db>(d.v());
    return Uint::d6(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::Dc>(d.v())) {
    const auto &[a0] = std::get<typename Uint::Dc>(d.v());
    return Uint::d8(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::Dd>(d.v())) {
    const auto &[a0] = std::get<typename Uint::Dd>(d.v());
    return Uint::da(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::De>(d.v())) {
    const auto &[a0] = std::get<typename Uint::De>(d.v());
    return Uint::dc(succ_double(*a0));
  } else {
    const auto &[a0] = std::get<typename Uint::Df>(d.v());
    return Uint::de(succ_double(*a0));
  }
}

Uint Little::succ_double(const Uint &d) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return Uint::d1(Uint::nil());
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return Uint::d1(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return Uint::d3(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return Uint::d5(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return Uint::d7(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return Uint::d9(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return Uint::db(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return Uint::dd(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return Uint::df(double_(*a0));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return Uint::d1(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::D9>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return Uint::d3(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::Da>(d.v())) {
    const auto &[a0] = std::get<typename Uint::Da>(d.v());
    return Uint::d5(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::Db>(d.v())) {
    const auto &[a0] = std::get<typename Uint::Db>(d.v());
    return Uint::d7(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::Dc>(d.v())) {
    const auto &[a0] = std::get<typename Uint::Dc>(d.v());
    return Uint::d9(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::Dd>(d.v())) {
    const auto &[a0] = std::get<typename Uint::Dd>(d.v());
    return Uint::db(succ_double(*a0));
  } else if (std::holds_alternative<typename Uint::De>(d.v())) {
    const auto &[a0] = std::get<typename Uint::De>(d.v());
    return Uint::dd(succ_double(*a0));
  } else {
    const auto &[a0] = std::get<typename Uint::Df>(d.v());
    return Uint::df(succ_double(*a0));
  }
}

} // namespace Hexadecimal
