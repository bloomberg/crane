#include "unit_void_edge.h"

void UnitVoidEdge::return_unit(uint64_t) { return; }

void UnitVoidEdge::count_down(uint64_t n) {
  if (n <= 0) {
    return;
  } else {
    uint64_t n_ = n - 1;
    count_down(n_);
    return;
  }
}

void UnitVoidEdge::id_unit_fn(uint64_t) {
  {
    id<std::monostate>(std::monostate{});
    return;
  }
}

uint64_t
UnitVoidEdge::match_option_unit(const std::optional<std::monostate> &o) {
  if (o.has_value()) {
    const std::monostate &_x = *o;
    return UINT64_C(1);
  } else {
    return UINT64_C(0);
  }
}

std::optional<std::monostate> UnitVoidEdge::return_some_tt(uint64_t n) {
  if (n == UINT64_C(0)) {
    return std::optional<std::monostate>();
  } else {
    return std::make_optional<std::monostate>(std::monostate{});
  }
}

void UnitVoidEdge::unit_chain(std::monostate u) {
  {
    std::move(u);
    return;
  }
}

void UnitVoidEdge::helper_void(uint64_t) { return; }

uint64_t UnitVoidEdge::use_helper(uint64_t n) { return n; }

uint64_t UnitVoidEdge::match_unit_nontail(std::monostate) {
  {
    return UINT64_C(7);
  }
}

void UnitVoidEdge::unit_to_unit_with_work(std::monostate) {
  {
    return;
  }
}

void UnitVoidEdge::seq_voids(uint64_t) { return; }

void UnitVoidEdge::conditional_unit(bool b) {
  if (b) {
    return;
  } else {
    return;
  }
}

uint64_t UnitVoidEdge::double_match_unit(std::monostate, std::monostate) {
  {
    {
      return UINT64_C(99);
    }
  }
}

UnitVoidEdge::tagged_nat UnitVoidEdge::make_tagged(uint64_t n) {
  return tagged_nat{n, std::monostate{}};
}

uint64_t UnitVoidEdge::get_value(const UnitVoidEdge::tagged_nat &t) {
  return t.tn_value;
}

void UnitVoidEdge::make_callback(uint64_t n, std::monostate) {
  return_unit(n);
  return;
}

void UnitVoidEdge::dummy_bool_void(bool) { return; }
