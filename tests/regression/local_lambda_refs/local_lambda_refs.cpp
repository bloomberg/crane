#include "local_lambda_refs.h"

uint64_t bump_twice(STRefs) {
  uint64_t r = UINT64_C(0);
  auto bump = [&](uint64_t k) -> void {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    while (true) {
      if (k <= 0) {
        return;
      } else {
        uint64_t k_ = k - 1;
        r = (r + UINT64_C(1));
        k = k_;
      }
    }
    return;
  };
  bump(UINT64_C(3));
  bump(UINT64_C(4));
  return r;
}

std::pair<uint64_t, uint64_t> bump_each(STRefs) {
  uint64_t r = UINT64_C(0);
  uint64_t s = UINT64_C(10);
  auto bump = [](uint64_t k, uint64_t *x_view) -> void {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    while (true) {
      if (k <= 0) {
        return;
      } else {
        uint64_t k_ = k - 1;
        uint64_t v = *x_view;
        *x_view = (v + UINT64_C(1));
        k = k_;
      }
    }
    return;
  };
  bump(UINT64_C(3), &r);
  bump(UINT64_C(4), &s);
  return std::make_pair(r, s);
}

std::pair<List<uint64_t>, List<uint64_t>> fill_each(STRefs) {
  std::shared_ptr<crane::array_storage<uint64_t>> a =
      std::make_shared<crane::array_storage<uint64_t>>(
          crane::st::extent(UINT64_C(3)), UINT64_C(0));
  std::shared_ptr<crane::array_storage<uint64_t>> b =
      std::make_shared<crane::array_storage<uint64_t>>(
          crane::st::extent(UINT64_C(2)), UINT64_C(0));
  auto fill = [](uint64_t i, uint64_t n, std::span<uint64_t> arr_view) -> void {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    while (true) {
      if (n <= 0) {
        return;
      } else {
        uint64_t n_ = n - 1;
        arr_view[i] = (i + UINT64_C(1));
        n = n_;
        i = (i + 1);
      }
    }
    return;
  };
  fill(UINT64_C(0), UINT64_C(3), std::span<uint64_t>{*a});
  fill(UINT64_C(0), UINT64_C(2), std::span<uint64_t>{*b});
  List<uint64_t> xs =
      crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{*a});
  List<uint64_t> ys =
      crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{*b});
  return std::make_pair(std::move(xs), std::move(ys));
}

uint64_t LocalLambdaRefs::nth(uint64_t n, const List<uint64_t> &l,
                              uint64_t default0) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return default0;
      } else {
        const auto &[a0, _] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        return a0;
      }
    } else {
      uint64_t m = n - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return default0;
      } else {
        const auto &[_, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        _loop_l = crane_raw(a10);
        n = m;
      }
    }
  }
}
