#include "stm.h"

uint64_t stmtest::stm_basic_counter() {
  stm::TVar<uint64_t> c = stm::newTVar<uint64_t>(UINT64_C(0));
  stm::writeTVar(c, UINT64_C(1));
  return stm::readTVar(c);
}

uint64_t stmtest::io_basic_counter() {
  return stm::atomically([&] { return stm_basic_counter(); });
}

uint64_t stmtest::stm_inc(uint64_t x) {
  stm::TVar<uint64_t> c = stm::newTVar<uint64_t>(x);
  STMDefs::template modify_tvar<uint64_t>(c,
                                          [](uint64_t n) { return (n + 1); });
  return stm::readTVar(c);
}

uint64_t stmtest::io_inc(uint64_t x) {
  return stm::atomically([&] { return stm_inc(x); });
}

uint64_t stmtest::stm_add_self(uint64_t x) {
  stm::TVar<uint64_t> c = stm::newTVar<uint64_t>(x);
  uint64_t v = stm::readTVar(c);
  stm::writeTVar(c, v + x);
  return stm::readTVar(c);
}

uint64_t stmtest::io_add_self(uint64_t x) {
  return stm::atomically([&] { return stm_add_self(x); });
}

void stmtest::stm_enqueue(const stm::TVar<List<uint64_t>> &q, uint64_t x) {
  List<uint64_t> xs = stm::readTVar(q);
  stm::writeTVar(q, xs.app(List<uint64_t>::cons(x, List<uint64_t>::nil())));
}

uint64_t stmtest::stm_dequeue(const stm::TVar<List<uint64_t>> &q) {
  List<uint64_t> xs = stm::readTVar(q);
  if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v_mut())) {
    return stm::retry<uint64_t>();
  } else {
    auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v_mut());
    stm::writeTVar(q, *a1);
    return std::move(a0);
  }
}

uint64_t stmtest::stm_tryDequeue(const stm::TVar<List<uint64_t>> &q,
                                 uint64_t dflt) {
  return stm::orElse<uint64_t>(stm_dequeue(q), dflt);
}

uint64_t stmtest::stm_queue_roundtrip(uint64_t x) {
  stm::TVar<List<uint64_t>> q =
      stm::newTVar<List<uint64_t>>(List<uint64_t>::nil());
  stm_enqueue(q, x);
  return stm_dequeue(std::move(q));
}

uint64_t stmtest::io_queue_roundtrip(uint64_t x) {
  return stm::atomically([&] { return stm_queue_roundtrip(x); });
}

uint64_t stmtest::stm_orElse_retry_example() {
  stm::TVar<List<uint64_t>> q =
      stm::newTVar<List<uint64_t>>(List<uint64_t>::nil());
  return stm::orElse<uint64_t>(stm_dequeue(std::move(q)), UINT64_C(42));
}

uint64_t stmtest::io_orElse_retry_example() {
  return stm::atomically([&] { return stm_orElse_retry_example(); });
}
