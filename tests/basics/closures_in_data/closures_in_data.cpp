#include "closures_in_data.h"

/// apply_all fns x applies every function in fns to x,
/// returning the list of results.
List<uint64_t>
ClosuresInData::apply_all(const List<std::function<uint64_t(uint64_t)>> &fns,
                          uint64_t x) {
  return fns.template map<uint64_t>(
      [=](std::function<uint64_t(uint64_t)> f) mutable { return f(x); });
}

uint64_t ClosuresInData::apply_forward(const ClosuresInData::transform &t,
                                       uint64_t x) {
  return t.forward(x);
}

uint64_t ClosuresInData::apply_backward(const ClosuresInData::transform &t,
                                        uint64_t x) {
  return t.backward(x);
}

/// compose_all fns x folds fns left, threading x through each
/// function in sequence.
uint64_t
ClosuresInData::compose_all(const List<std::function<uint64_t(uint64_t)>> &fns,
                            uint64_t x) {
  return fns.template fold_left<uint64_t>(
      [](uint64_t acc, std::function<uint64_t(uint64_t)> f) { return f(acc); },
      x);
}

/// maybe_apply mf x applies function mf to x if present,
/// otherwise returns x unchanged.
uint64_t ClosuresInData::maybe_apply(
    const std::optional<std::function<uint64_t(uint64_t)>> &mf, uint64_t x) {
  if (mf.has_value()) {
    const std::function<uint64_t(uint64_t)> &f = *mf;
    return f(x);
  } else {
    return x;
  }
}
