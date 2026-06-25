#include "monadic.h"

std::optional<uint64_t> Monadic::safe_div(uint64_t n, uint64_t m) {
  if (m <= 0) {
    return std::optional<uint64_t>();
  } else {
    uint64_t m_ = m - 1;
    return std::make_optional<uint64_t>(((m_ + 1) ? n / (m_ + 1) : 0));
  }
}

std::optional<uint64_t> Monadic::safe_sub(uint64_t n, uint64_t m) {
  if (n < m) {
    return std::optional<uint64_t>();
  } else {
    return std::make_optional<uint64_t>((((n - m) > n ? 0 : (n - m))));
  }
}

std::optional<uint64_t> Monadic::div_then_sub(uint64_t a, uint64_t b,
                                              uint64_t c) {
  return option_bind<uint64_t, uint64_t>(
      safe_div(a, b), [=](uint64_t x) mutable {
        return option_bind<uint64_t, uint64_t>(safe_sub(x, c),
                                               option_return<uint64_t>);
      });
}

Monadic::State<std::pair<uint64_t, uint64_t>, std::monostate>
Monadic::fib_state(uint64_t n) {
  return ListDef::seq(UINT64_C(0), n)
      .template fold_left<
          Monadic::State<std::pair<uint64_t, uint64_t>, std::monostate>>(
          [](std::function<
                 std::pair<std::monostate, std::pair<uint64_t, uint64_t>>(
                     std::pair<uint64_t, uint64_t>)>
                 acc,
             uint64_t) {
            return state_bind<std::pair<uint64_t, uint64_t>, std::monostate,
                              std::monostate>(acc, [](std::monostate) {
              return state_bind<std::pair<uint64_t, uint64_t>,
                                std::pair<uint64_t, uint64_t>, std::monostate>(
                  state_get<std::pair<uint64_t, uint64_t>>(),
                  [](std::pair<uint64_t, uint64_t> pat) {
                    const uint64_t &a = pat.first;
                    const uint64_t &b = pat.second;
                    return state_put<std::pair<uint64_t, uint64_t>>(
                        std::make_pair(b, (a + b)));
                  });
            });
          },
          state_return<std::pair<uint64_t, uint64_t>, std::monostate>(
              std::monostate{}));
}

uint64_t Monadic::fib(uint64_t n) {
  if (n <= UINT64_C(2)) {
    return n;
  } else {
    auto _cs = fib_state(n)(std::make_pair(UINT64_C(0), UINT64_C(1)));
    std::monostate _x = std::move(_cs.first);
    std::pair<uint64_t, uint64_t> p = std::move(_cs.second);
    uint64_t a = std::move(p.first);
    uint64_t _x0 = std::move(p.second);
    return a;
  }
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
