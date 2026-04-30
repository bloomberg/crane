#include <graph.h>

/// A graph abstraction parameterized by a container type G and
/// node type A. Provides operations for building and querying
/// the graph.
bool nat_eqb(const Nat &n, const Nat &m) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[d_a0] = std::get<typename Nat::S>(n.v());
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return false;
    } else {
      const auto &[d_a00] = std::get<typename Nat::S>(m.v());
      return nat_eqb(*(d_a0), *(d_a00));
    }
  }
}
