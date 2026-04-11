#include <stream.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>
#include <vector>

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

int nat_to_int(const std::shared_ptr<Nat> &n) {
  return std::visit(
      Overloaded{[](const Nat::O) -> int { return 0; },
                 [](const Nat::S s) -> int { return 1 + nat_to_int(s.d_a0); }},
      n->v());
}

template <typename A>
std::vector<A> list_to_vec(const std::shared_ptr<List<A>> &l) {
  std::vector<A> result;
  auto cur = l;
  while (true) {
    bool done = std::visit(
        Overloaded{[&](const typename List<A>::Nil) -> bool { return true; },
                   [&](const typename List<A>::Cons c) -> bool {
                     result.push_back(c.d_a0);
                     cur = c.d_a1;
                     return false;
                   }},
        cur->v());
    if (done)
      break;
  }
  return result;
}

std::shared_ptr<Nat> int_to_nat(int x) {
  if (x <= 0)
    return Nat::o();
  return Nat::s(int_to_nat(x - 1));
}

using NatStream = Stream<std::shared_ptr<Nat>>;

int main() {
  // Test 1: first_five_nats should be [0, 1, 2, 3, 4]
  auto nats_list = NatStream::first_five_nats();
  auto vec = list_to_vec<std::shared_ptr<Nat>>(nats_list);
  ASSERT(vec.size() == 5);
  for (size_t i = 0; i < 5; i++) {
    ASSERT(nat_to_int(vec[i]) == static_cast<int>(i));
  }

  // Test 2: first_five_ones should be [1, 1, 1, 1, 1]
  auto ones_list = NatStream::first_five_ones();
  auto vec_ones = list_to_vec<std::shared_ptr<Nat>>(ones_list);
  ASSERT(vec_ones.size() == 5);
  for (size_t i = 0; i < 5; i++) {
    ASSERT(nat_to_int(vec_ones[i]) == 1);
  }

  // Test 3: interleaved should be [0, 7, 1, 7, 2, 7, 3, 7]
  auto interleaved_list = NatStream::interleaved();
  auto vec_i = list_to_vec<std::shared_ptr<Nat>>(interleaved_list);
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
  auto ten_list = stream10->take(int_to_nat(3));
  auto vec10 = list_to_vec<std::shared_ptr<Nat>>(ten_list);
  ASSERT(vec10.size() == 3);
  ASSERT(nat_to_int(vec10[0]) == 10);
  ASSERT(nat_to_int(vec10[1]) == 11);
  ASSERT(nat_to_int(vec10[2]) == 12);

  // Test 5: repeat creates infinite constant stream
  auto fives = NatStream::repeat<std::shared_ptr<Nat>>(int_to_nat(5));
  auto five_list = fives->take(int_to_nat(4));
  auto vec5 = list_to_vec<std::shared_ptr<Nat>>(five_list);
  ASSERT(vec5.size() == 4);
  for (int i = 0; i < 4; i++) {
    ASSERT(nat_to_int(vec5[i]) == 5);
  }

  // Test 6: interleave of two infinite streams (called as method)
  auto evens = NatStream::nats_from(int_to_nat(0));
  auto odds = NatStream::nats_from(int_to_nat(100));
  auto mixed = evens->interleave(odds);
  auto mixed_list = mixed->take(int_to_nat(6));
  auto vec_m = list_to_vec<std::shared_ptr<Nat>>(mixed_list);
  ASSERT(vec_m.size() == 6);
  ASSERT(nat_to_int(vec_m[0]) == 0);
  ASSERT(nat_to_int(vec_m[1]) == 100);
  ASSERT(nat_to_int(vec_m[2]) == 1);
  ASSERT(nat_to_int(vec_m[3]) == 101);
  ASSERT(nat_to_int(vec_m[4]) == 2);
  ASSERT(nat_to_int(vec_m[5]) == 102);

  return testStatus;
}
