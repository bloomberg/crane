#include "unit_void_edge2.h"

uint64_t UnitVoidEdge2::take_unit(std::monostate) { return UINT64_C(42); }

void UnitVoidEdge2::opaque_unit(uint64_t) { return; }

uint64_t UnitVoidEdge2::let_use_as_arg(uint64_t n) {
  opaque_unit(n);
  std::monostate x = std::monostate{};
  return take_unit(x);
}

void UnitVoidEdge2::let_return_unit(uint64_t _x0) {
  opaque_unit(_x0);
  return;
}

uint64_t UnitVoidEdge2::let_match_unit(uint64_t n) {
  opaque_unit(n);
  std::monostate x = std::monostate{};
  {
    return n;
  }
}

uint64_t UnitVoidEdge2::let_chain_use(uint64_t n) {
  opaque_unit(n);
  std::monostate a = std::monostate{};
  return take_unit(a);
}

uint64_t UnitVoidEdge2::let_use_in_if(uint64_t n, bool flag) {
  opaque_unit(n);
  std::monostate x = std::monostate{};
  if (flag) {
    return take_unit(x);
  } else {
    return UINT64_C(0);
  }
}

void UnitVoidEdge2::mono_bind_return() {
  std::cout << "hello"s;
  return;
}

void UnitVoidEdge2::mono_bind_rebind() {
  std::cout << "hi"s;
  return;
}

void UnitVoidEdge2::mono_chain() {
  std::cout << "a"s;
  std::cout << "b"s;
  return;
}

uint64_t UnitVoidEdge2::mono_bind_match() {
  std::cout << "test"s;
  std::monostate x = std::monostate{};
  {
    return UINT64_C(42);
  }
}

uint64_t UnitVoidEdge2::mono_bind_opaque() {
  std::cout << "setup"s;
  return UINT64_C(99);
}

void UnitVoidEdge2::count_down_unit(uint64_t n) {
  if (n <= 0) {
    return;
  } else {
    uint64_t n_ = n - 1;
    count_down_unit(n_);
    return;
  }
}

std::optional<std::monostate> UnitVoidEdge2::make_some_unit(bool b) {
  if (b) {
    return std::make_optional<std::monostate>(std::monostate{});
  } else {
    return std::optional<std::monostate>();
  }
}

uint64_t
UnitVoidEdge2::use_option_unit(const std::optional<std::monostate> &o) {
  if (o.has_value()) {
    const std::monostate &u = *o;
    return take_unit(u);
  } else {
    return UINT64_C(0);
  }
}

uint64_t UnitVoidEdge2::compose_option_unit(bool b1, bool b2) {
  std::optional<std::monostate> o1 = make_some_unit(b1);
  std::optional<std::monostate> o2 = make_some_unit(b2);
  return (use_option_unit(o1) + use_option_unit(o2));
}

UnitVoidEdge2::pair<uint64_t, std::monostate>
UnitVoidEdge2::make_nat_unit_pair(uint64_t n) {
  return pair<uint64_t, std::monostate>::pair0(n, std::monostate{});
}
