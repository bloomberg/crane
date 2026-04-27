#include <unit_void_edge.h>

void UnitVoidEdge::return_unit(const unsigned int &) { return; }

void UnitVoidEdge::count_down(const unsigned int &n) {
  if (n <= 0) {
    return;
  } else {
    unsigned int n_ = n - 1;
    count_down(n_);
    return;
  }
}

void UnitVoidEdge::id_unit_fn(const unsigned int &) {
  {
    id<std::monostate>(std::monostate{});
    return;
  }
}

__attribute__((pure)) unsigned int
UnitVoidEdge::match_option_unit(const std::optional<std::monostate> &o) {
  if (o.has_value()) {
    const std::monostate &_x = *o;
    return 1u;
  } else {
    return 0u;
  }
}

__attribute__((pure)) std::optional<std::monostate>
UnitVoidEdge::return_some_tt(const unsigned int &n) {
  if (n == 0u) {
    return std::optional<std::monostate>();
  } else {
    return std::make_optional<std::monostate>(std::monostate{});
  }
}

void UnitVoidEdge::unit_chain(std::monostate) { return; }

void UnitVoidEdge::helper_void(const unsigned int &) { return; }

__attribute__((pure)) unsigned int UnitVoidEdge::use_helper(unsigned int n) {
  return n;
}

__attribute__((pure)) unsigned int
UnitVoidEdge::match_unit_nontail(const std::monostate &) {
  {
    return 7u;
  }
}

void UnitVoidEdge::unit_to_unit_with_work(const std::monostate &) {
  {
    return;
  }
}

void UnitVoidEdge::seq_voids(const unsigned int &) { return; }

void UnitVoidEdge::conditional_unit(const bool &b) {
  if (b) {
    return;
  } else {
    return;
  }
}

__attribute__((pure)) unsigned int
UnitVoidEdge::double_match_unit(const std::monostate &,
                                const std::monostate &) {
  {
    {
      return 99u;
    }
  }
}

__attribute__((pure)) UnitVoidEdge::tagged_nat
UnitVoidEdge::make_tagged(unsigned int n) {
  return tagged_nat{n, std::monostate{}};
}

__attribute__((pure)) unsigned int
UnitVoidEdge::get_value(const UnitVoidEdge::tagged_nat &t) {
  return t.tn_value;
}

void UnitVoidEdge::make_callback(const unsigned int &n,
                                 const std::monostate &) {
  return_unit(n);
  return;
}

void UnitVoidEdge::dummy_bool_void(const bool &) { return; }
