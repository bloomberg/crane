#include <unit_void_edge2.h>

#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
UnitVoidEdge2::take_unit(const std::monostate _x) {
  return 42u;
}

void UnitVoidEdge2::opaque_unit(const unsigned int _x) { return; }

__attribute__((pure)) unsigned int
UnitVoidEdge2::let_use_as_arg(const unsigned int n) {
  opaque_unit(n);
  std::monostate x = std::monostate{};
  return take_unit(x);
}

void UnitVoidEdge2::let_return_unit(const unsigned int _x0) {
  {
    opaque_unit(_x0);
    return;
  }
}

__attribute__((pure)) unsigned int
UnitVoidEdge2::let_match_unit(const unsigned int n) {
  opaque_unit(std::move(n));
  std::monostate x = std::monostate{};
  {
    return n;
  }
}

__attribute__((pure)) unsigned int
UnitVoidEdge2::let_chain_use(const unsigned int n) {
  opaque_unit(n);
  std::monostate a = std::monostate{};
  return take_unit(a);
}

__attribute__((pure)) unsigned int
UnitVoidEdge2::let_use_in_if(const unsigned int n, const bool flag) {
  opaque_unit(n);
  std::monostate x = std::monostate{};
  if (flag) {
    return take_unit(x);
  } else {
    return 0u;
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

unsigned int UnitVoidEdge2::mono_bind_match() {
  std::cout << "test"s;
  std::monostate x = std::monostate{};
  {
    return 42u;
  }
}

unsigned int UnitVoidEdge2::mono_bind_opaque() {
  std::cout << "setup"s;
  return 99u;
}

void UnitVoidEdge2::count_down_unit(const unsigned int n) {
  if (n <= 0) {
    return;
  } else {
    unsigned int n_ = n - 1;
    {
      count_down_unit(n_);
      return;
    }
  }
}

__attribute__((pure)) std::optional<std::monostate>
UnitVoidEdge2::make_some_unit(const bool b) {
  if (b) {
    return std::make_optional<std::monostate>(std::monostate{});
  } else {
    return std::optional<std::monostate>();
  }
}

__attribute__((pure)) unsigned int
UnitVoidEdge2::use_option_unit(const std::optional<std::monostate> o) {
  if (o.has_value()) {
    std::monostate u = *o;
    return take_unit(u);
  } else {
    return 0u;
  }
}

__attribute__((pure)) unsigned int
UnitVoidEdge2::compose_option_unit(const bool b1, const bool b2) {
  std::optional<std::monostate> o1 = make_some_unit(b1);
  std::optional<std::monostate> o2 = make_some_unit(b2);
  return (use_option_unit(std::move(o1)) + use_option_unit(std::move(o2)));
}

std::shared_ptr<UnitVoidEdge2::pair<unsigned int, std::monostate>>
UnitVoidEdge2::make_nat_unit_pair(const unsigned int n) {
  return pair<unsigned int, std::monostate>::pair0(std::move(n),
                                                   std::monostate{});
}
