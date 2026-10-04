#include "NumOps.h"

#include "Num.h"

namespace NumOps {

bool leb(const Num::Num &a, const Num::Num &b) {
  if (std::holds_alternative<typename Num::Num::Zero>(a.v())) {
    return true;
  } else {
    const auto &[n] = std::get<typename Num::Num::Succ>(a.v());
    if (std::holds_alternative<typename Num::Num::Zero>(b.v())) {
      return false;
    } else {
      const auto &[n0] = std::get<typename Num::Num::Succ>(b.v());
      return leb(*n, *n0);
    }
  }
}

} // namespace NumOps
