#include "loopify_adopted_fix_alias_result.h"

/// A machine adopting a local fixpoint that calls back into its function,
/// the function's result written through a type abbreviation -- the shape
/// of FMapList.map2 and combine.
///
/// The function returns t C; extraction gives the fixpoint the unfolded
/// list (nat * C), and the C++ spells the two t<T3> and
/// List<std::pair<uint64_t, T3>>.  The frame transform once told
/// them apart by that spelling, dropped the adoption the plan had made,
/// and left map2 the recursion it is.
std::optional<uint64_t>
LoopifyAdoptedFixAliasResult::add_opt(std::optional<uint64_t> a,
                                      std::optional<uint64_t> b) {
  if (a.has_value()) {
    const uint64_t &x = *a;
    if (b.has_value()) {
      const uint64_t &y = *b;
      return std::make_optional<uint64_t>((x + y));
    } else {
      return std::make_optional<uint64_t>(x);
    }
  } else {
    if (b.has_value()) {
      const uint64_t &x = *b;
      return std::make_optional<uint64_t>(x);
    } else {
      return std::optional<uint64_t>();
    }
  }
}

uint64_t LoopifyAdoptedFixAliasResult::sum(
    const List<std::pair<uint64_t, uint64_t>> &m) {
  return m.template fold_left<uint64_t>(
      [](uint64_t acc,
         std::pair<uint64_t, uint64_t> p) { return (acc + p.second); },
      UINT64_C(0));
}

/// The keys i * step, ..., (i + n - 1) * step, each bound to its
/// multiple.
LoopifyAdoptedFixAliasResult::t<uint64_t>
LoopifyAdoptedFixAliasResult::keys(uint64_t n, uint64_t i, uint64_t step) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyAdoptedFixAliasResult::t<uint64_t>> _root{};
  std::shared_ptr<LoopifyAdoptedFixAliasResult::t<uint64_t>> *_write = nullptr;
  while (true) {
    if (n <= 0) {
      auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
      (_write ? *(*_write = std::make_shared<
                      LoopifyAdoptedFixAliasResult::t<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = n - 1;
      auto _cell = typename List<std::pair<uint64_t, uint64_t>>::Cons(
          std::make_pair((i * step), i), nullptr);
      LoopifyAdoptedFixAliasResult::t<uint64_t> &_node =
          (_write ? *(*_write = std::make_shared<
                          LoopifyAdoptedFixAliasResult::t<uint64_t>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
              _node.v_mut())
              .l;
      i = (i + 1);
      n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

LoopifyAdoptedFixAliasResult::t<uint64_t>
LoopifyAdoptedFixAliasResult::merged(uint64_t n) {
  return map2<uint64_t, uint64_t, uint64_t>(add_opt,
                                            keys(n, UINT64_C(0), UINT64_C(2)),
                                            keys(n, UINT64_C(0), UINT64_C(3)));
}
