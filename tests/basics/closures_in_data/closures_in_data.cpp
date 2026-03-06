#include <algorithm>
#include <any>
#include <cassert>
#include <closures_in_data.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> ClosuresInData::apply_all(
    const std::shared_ptr<List<std::function<unsigned int(unsigned int)>>> &fns,
    const unsigned int x) {
  return fns->template map<unsigned int>(
      [&](std::function<unsigned int(unsigned int)> f) { return f(x); });
}

unsigned int ClosuresInData::apply_forward(
    const std::shared_ptr<ClosuresInData::transform> &t, const unsigned int x) {
  return t->forward(x);
}

unsigned int ClosuresInData::apply_backward(
    const std::shared_ptr<ClosuresInData::transform> &t, const unsigned int x) {
  return t->backward(x);
}

unsigned int ClosuresInData::compose_all(
    const std::shared_ptr<List<std::function<unsigned int(unsigned int)>>> &fns,
    const unsigned int x) {
  return fns->template fold_left<unsigned int>(
      [](unsigned int acc, std::function<unsigned int(unsigned int)> f) {
        return f(acc);
      },
      x);
}

unsigned int ClosuresInData::maybe_apply(
    const std::optional<std::function<unsigned int(unsigned int)>> mf,
    const unsigned int x) {
  if (mf.has_value()) {
    std::function<unsigned int(unsigned int)> f = *mf;
    return std::move(f)(x);
  } else {
    return std::move(x);
  }
}

std::pair<unsigned int, unsigned int> Nat::divmod(const unsigned int x,
                                                  const unsigned int y,
                                                  const unsigned int q,
                                                  const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(std::move(q), std::move(u));
  } else {
    unsigned int x_ = x - 1;
    if (u <= 0) {
      return Nat::divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return Nat::divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

unsigned int Nat::div(const unsigned int x, const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0, y_).first;
  }
}
