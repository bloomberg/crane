#include <unit_void_edge.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

void UnitVoidEdge::return_unit(const unsigned int _x) { return; }

void UnitVoidEdge::count_down(const unsigned int n) {
  if (n <= 0) {
    return;
  } else {
    unsigned int n_ = n - 1;
    count_down(n_);
    return;
  }
}

void UnitVoidEdge::id_unit_fn(const unsigned int _x) {
  {
    id<std::monostate>(std::monostate{});
    return;
  }
}

__attribute__((pure)) unsigned int
UnitVoidEdge::match_option_unit(const std::optional<std::monostate> o) {
  if (o.has_value()) {
    std::monostate _x = *o;
    return 1u;
  } else {
    return 0u;
  }
}

__attribute__((pure)) std::optional<std::monostate>
UnitVoidEdge::return_some_tt(const unsigned int n) {
  if (n == 0u) {
    return std::optional<std::monostate>();
  } else {
    return std::make_optional<std::monostate>(std::monostate{});
  }
}

void UnitVoidEdge::unit_chain(const std::monostate u) {
  {
    std::move(u);
    return;
  }
}

void UnitVoidEdge::helper_void(const unsigned int _x) { return; }

__attribute__((pure)) unsigned int
UnitVoidEdge::use_helper(const unsigned int n) {
  return std::move(n);
}

__attribute__((pure)) unsigned int
UnitVoidEdge::match_unit_nontail(const std::monostate u) {
  {
    return 7u;
  }
}

void UnitVoidEdge::unit_to_unit_with_work(const std::monostate u) {
  {
    return;
  }
}

void UnitVoidEdge::seq_voids(const unsigned int _x) { return; }

void UnitVoidEdge::conditional_unit(const bool b) {
  if (b) {
    return;
  } else {
    return;
  }
}

__attribute__((pure)) unsigned int
UnitVoidEdge::double_match_unit(const std::monostate u1,
                                const std::monostate u2) {
  {
    {
      return 99u;
    }
  }
}

std::shared_ptr<UnitVoidEdge::tagged_nat>
UnitVoidEdge::make_tagged(const unsigned int n) {
  return std::make_shared<UnitVoidEdge::tagged_nat>(
      tagged_nat{std::move(n), std::monostate{}});
}

__attribute__((pure)) unsigned int
UnitVoidEdge::get_value(const std::shared_ptr<UnitVoidEdge::tagged_nat> &t) {
  return t->tn_value;
}

void UnitVoidEdge::make_callback(const unsigned int n,
                                 const std::monostate _x) {
  return_unit(n);
  return;
}

void UnitVoidEdge::dummy_bool_void(const bool _x) { return; }
