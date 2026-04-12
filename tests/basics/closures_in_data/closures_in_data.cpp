#include <closures_in_data.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// apply_all fns x applies every function in fns to x,
/// returning the list of results.
std::shared_ptr<List<unsigned int>> ClosuresInData::apply_all(
    const std::shared_ptr<List<std::function<unsigned int(unsigned int)>>> &fns,
    const unsigned int x) {
  return fns->template map<unsigned int>(
      [=](const std::function<unsigned int(unsigned int)> f) mutable {
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
      [](const unsigned int acc,
         const std::function<unsigned int(unsigned int)> f) { return f(acc); },
      x);
}

/// maybe_apply mf x applies function mf to x if present,
/// otherwise returns x unchanged.
__attribute__((pure)) unsigned int ClosuresInData::maybe_apply(
    const std::optional<std::function<unsigned int(unsigned int)>> mf,
    const unsigned int x) {
  if (mf.has_value()) {
    const std::function<unsigned int(unsigned int)> &f = *mf;
    return f(x);
  } else {
    return x;
  }
}
