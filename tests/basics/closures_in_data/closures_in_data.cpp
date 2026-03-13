#include <closures_in_data.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

/// apply_all fns x applies every function in fns to x,
/// returning the list of results.
std::shared_ptr<List<unsigned int>> ClosuresInData::apply_all(
    const std::shared_ptr<List<std::function<unsigned int(unsigned int)>>> &fns,
    const unsigned int x) {
  return fns->template map<unsigned int>(
      [=](std::function<unsigned int(unsigned int)> f) mutable {
        return f(x);
      });
}

__attribute__((pure)) unsigned int ClosuresInData::apply_forward(
    const std::shared_ptr<ClosuresInData::transform> &t, const unsigned int x) {
  return t->forward(x);
}

__attribute__((pure)) unsigned int ClosuresInData::apply_backward(
    const std::shared_ptr<ClosuresInData::transform> &t, const unsigned int x) {
  return t->backward(x);
}

/// compose_all fns x folds fns left, threading x through each
/// function in sequence.
__attribute__((pure)) unsigned int ClosuresInData::compose_all(
    const std::shared_ptr<List<std::function<unsigned int(unsigned int)>>> &fns,
    const unsigned int x) {
  return fns->template fold_left<unsigned int>(
      [](unsigned int acc, std::function<unsigned int(unsigned int)> f) {
        return f(acc);
      },
      x);
}

/// maybe_apply mf x applies function mf to x if present,
/// otherwise returns x unchanged.
__attribute__((pure)) unsigned int ClosuresInData::maybe_apply(
    const std::optional<std::function<unsigned int(unsigned int)>> mf,
    const unsigned int x) {
  if (mf.has_value()) {
    std::function<unsigned int(unsigned int)> f = *mf;
    return std::move(f)(x);
  } else {
    return std::move(x);
  }
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
Nat::divmod(const unsigned int x, const unsigned int y, const unsigned int q,
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

__attribute__((pure)) unsigned int Nat::div(const unsigned int x,
                                            const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
