#include <stream.h>

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

using NatStream = Stream<Nat>;

int main() {
  // Test 1: first_five_nats should be [0, 1, 2, 3, 4]
  auto nats_list = NatStream::first_five_nats();
  auto vec = list_to_vec<Nat>(nats_list);
  ASSERT(vec.size() == 5);
  for (size_t i = 0; i < 5; i++) {
    ASSERT(nat_to_int(vec[i]) == static_cast<int>(i));
  }

  // Test 2: first_five_ones should be [1, 1, 1, 1, 1]
  auto ones_list = NatStream::first_five_ones();
  auto vec_ones = list_to_vec<Nat>(ones_list);
  ASSERT(vec_ones.size() == 5);
  for (size_t i = 0; i < 5; i++) {
    ASSERT(nat_to_int(vec_ones[i]) == 1);
  }

  // Test 3: interleaved should be [0, 7, 1, 7, 2, 7, 3, 7]
  auto interleaved_list = NatStream::interleaved();
  auto vec_i = list_to_vec<Nat>(interleaved_list);
  ASSERT(vec_i.size() == 8);
  ASSERT(nat_to_int(vec_i[0]) == 0);
  ASSERT(nat_to_int(vec_i[1]) == 7);
  ASSERT(nat_to_int(vec_i[2]) == 1);
  ASSERT(nat_to_int(vec_i[3]) == 7);
  ASSERT(nat_to_int(vec_i[4]) == 2);
  ASSERT(nat_to_int(vec_i[5]) == 7);
  ASSERT(nat_to_int(vec_i[6]) == 3);
  ASSERT(nat_to_int(vec_i[7]) == 7);

  // Test 4: nats_from creates infinite stream that doesn't diverge
  auto stream10 = NatStream::nats_from(int_to_nat(10));
  auto ten_list = NatStream::take(int_to_nat(3), stream10);
  auto vec10 = list_to_vec<Nat>(ten_list);
  ASSERT(vec10.size() == 3);
  ASSERT(nat_to_int(vec10[0]) == 10);
  ASSERT(nat_to_int(vec10[1]) == 11);
  ASSERT(nat_to_int(vec10[2]) == 12);

  // Test 5: repeat creates infinite constant stream
  auto fives = NatStream::repeat<Nat>(int_to_nat(5));
  auto five_list = NatStream::take(int_to_nat(4), fives);
  auto vec5 = list_to_vec<Nat>(five_list);
  ASSERT(vec5.size() == 4);
  for (int i = 0; i < 4; i++) {
    ASSERT(nat_to_int(vec5[i]) == 5);
  }

  // Test 6: interleave of two infinite streams (called as method)
  auto evens = NatStream::nats_from(int_to_nat(0));
  auto odds = NatStream::nats_from(int_to_nat(100));
  auto mixed = evens.interleave(odds);
  auto mixed_list = NatStream::take(int_to_nat(6), mixed);
  auto vec_m = list_to_vec<Nat>(mixed_list);
  ASSERT(vec_m.size() == 6);
  ASSERT(nat_to_int(vec_m[0]) == 0);
  ASSERT(nat_to_int(vec_m[1]) == 100);
  ASSERT(nat_to_int(vec_m[2]) == 1);
  ASSERT(nat_to_int(vec_m[3]) == 101);
  ASSERT(nat_to_int(vec_m[4]) == 2);
  ASSERT(nat_to_int(vec_m[5]) == 102);

  return testStatus;
}
