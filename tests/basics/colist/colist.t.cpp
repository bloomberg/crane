#include <colist.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>
#include <vector>

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int nat_to_int(const Nat &n) {
  return std::visit(
      Overloaded{[](const Nat::O) -> int { return 0; },
                 [](const Nat::S &s) -> int { return 1 + nat_to_int(*s.d_a0); }},
      n.v());
}

template <typename A>
std::vector<A> list_to_vec(const List<A> &l) {
  std::vector<A> result;
  const List<A> *current = &l;
  while (true) {
    if (std::holds_alternative<typename List<A>::Nil>(current->v())) {
      break;
    }
    const auto &[head, tail] = std::get<typename List<A>::Cons>(current->v());
    result.push_back(head);
    current = tail.get();
  }
  return result;
}

Nat int_to_nat(int x) {
  Nat result = Nat::o();
  for (int i = 0; i < x; i++) {
    result = Nat::s(std::move(result));
  }
  return result;
}

using NatColist = Colist<Nat>;

int main() {
  // Test 1: first_three should be [0, 1, 2]
  auto ft = NatColist::first_three();
  auto vec = list_to_vec<Nat>(ft);
  ASSERT(vec.size() == 3);
  ASSERT(nat_to_int(vec[0]) == 0);
  ASSERT(nat_to_int(vec[1]) == 1);
  ASSERT(nat_to_int(vec[2]) == 2);

  // Test 2: nats creates an infinite stream that doesn't diverge
  auto stream = NatColist::nats(Nat::o());
  // Converting 5 elements should work without stack overflow
  auto five = NatColist::list_of_colist(int_to_nat(5), stream);
  auto vec5 = list_to_vec<Nat>(five);
  ASSERT(vec5.size() == 5);
  ASSERT(nat_to_int(vec5[0]) == 0);
  ASSERT(nat_to_int(vec5[1]) == 1);
  ASSERT(nat_to_int(vec5[2]) == 2);
  ASSERT(nat_to_int(vec5[3]) == 3);
  ASSERT(nat_to_int(vec5[4]) == 4);

  // Test 3: nats starting from a non-zero value
  auto stream5 = NatColist::nats(int_to_nat(5));
  auto three = NatColist::list_of_colist(int_to_nat(3), stream5);
  auto vec3 = list_to_vec<Nat>(three);
  ASSERT(vec3.size() == 3);
  ASSERT(nat_to_int(vec3[0]) == 5);
  ASSERT(nat_to_int(vec3[1]) == 6);
  ASSERT(nat_to_int(vec3[2]) == 7);

  return testStatus;
}
