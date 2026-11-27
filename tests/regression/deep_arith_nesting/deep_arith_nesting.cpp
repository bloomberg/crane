#include "deep_arith_nesting.h"

/// 1200 additions: deeper than clang's 1024-bracket limit.
uint64_t DeepArithNesting::bump(uint64_t x) {
  return [&]() {
    auto _lit0 =
        x + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1);
    auto _lit1 =
        _lit0 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit2 =
        _lit1 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit3 =
        _lit2 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit4 =
        _lit3 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit5 =
        _lit4 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit6 =
        _lit5 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit7 =
        _lit6 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit8 =
        _lit7 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit9 =
        _lit8 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit10 =
        _lit9 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit11 =
        _lit10 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit12 =
        _lit11 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit13 =
        _lit12 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit14 =
        _lit13 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit15 =
        _lit14 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit16 =
        _lit15 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit17 =
        _lit16 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit18 =
        _lit17 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit19 =
        _lit18 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit20 =
        _lit19 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit21 =
        _lit20 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit22 =
        _lit21 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit23 =
        _lit22 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit24 =
        _lit23 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit25 =
        _lit24 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit26 =
        _lit25 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit27 =
        _lit26 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit28 =
        _lit27 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit29 =
        _lit28 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit30 =
        _lit29 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit31 =
        _lit30 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit32 =
        _lit31 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit33 =
        _lit32 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit34 =
        _lit33 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit35 =
        _lit34 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit36 =
        _lit35 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit37 =
        _lit36 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    auto _lit38 =
        _lit37 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
        UINT64_C(1);
    return _lit38 + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
           UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
           UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
           UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
           UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) +
           UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1) + UINT64_C(1);
  }();
}
