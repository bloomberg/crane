#include "local_cofix_without_parameters.h"

uint64_t
LocalCofixWithoutParameters::hd(const LocalCofixWithoutParameters::stream &s) {
  const auto &[a0, a1] =
      std::get<typename LocalCofixWithoutParameters::stream::Cons>(s.v());
  return a0;
}

List<uint64_t> LocalCofixWithoutParameters::take(
    uint64_t k, const LocalCofixWithoutParameters::stream &s) {
  if (k <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t k_ = k - 1;
    const auto &[a0, a1] =
        std::get<typename LocalCofixWithoutParameters::stream::Cons>(s.v());
    return List<uint64_t>::cons(a0, take(k_, a1));
  }
}

LocalCofixWithoutParameters::stream
LocalCofixWithoutParameters::zeros_or(bool b) {
  if (b) {
    auto z_impl = [=](auto &) { return stream::cons(UINT64_C(0), z); };
    auto z = [=, z_impl = std::move(z_impl)]() { z_impl(z_impl); };
    return z;
  } else {
    auto o_impl = [=](auto &) { return stream::cons(UINT64_C(1), o); };
    auto o = [=, o_impl = std::move(o_impl)]() { o_impl(o_impl); };
    return o;
  }
}

LocalCofixWithoutParameters::stream
LocalCofixWithoutParameters::ones_then(const List<uint64_t> &l) {
  return l.template fold_right<LocalCofixWithoutParameters::stream>(
      [](uint64_t x, const LocalCofixWithoutParameters::stream &x0) {
        return stream::cons(x, x0);
      },
      []() {
        auto o_impl = [=](auto &) { return stream::cons(UINT64_C(1), o); };
        auto o = [=]() { o_impl(o_impl); };
        return o;
      }());
}
