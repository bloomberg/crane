#include <stm.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <stm_adapter.h>
#include <type_traits>
#include <utility>
#include <variant>

unsigned int stmtest::stm_basic_counter(const std::monostate) {
  stm::TVar<unsigned int> c = stm::newTVar(0u);
  stm::writeTVar(c, 1u);
  return stm::readTVar(c);
}

unsigned int stmtest::io_basic_counter() {
  return stm::atomically([&] { return stm_basic_counter(std::monostate{}); });
}

unsigned int stmtest::stm_inc(const unsigned int x) {
  stm::TVar<unsigned int> c = stm::newTVar(x);
  STMDefs::template modifyTVar<unsigned int>(
      c, [](unsigned int n) { return (n + 1); });
  return stm::readTVar(c);
}

unsigned int stmtest::io_inc(const unsigned int x) {
  return stm::atomically([&] { return stm_inc(x); });
}

unsigned int stmtest::stm_add_self(const unsigned int x) {
  stm::TVar<unsigned int> c = stm::newTVar(x);
  unsigned int v = stm::readTVar(c);
  stm::writeTVar(c, (v + x));
  return stm::readTVar(c);
}

unsigned int stmtest::io_add_self(const unsigned int x) {
  return stm::atomically([&] { return stm_add_self(x); });
}

void stmtest::stm_enqueue(
    const stm::TVar<std::shared_ptr<List<unsigned int>>> q,
    const unsigned int x) {
  std::shared_ptr<List<unsigned int>> xs = stm::readTVar(q);
  stm::writeTVar(q, std::move(xs)->app(List<unsigned int>::cons(
                        x, List<unsigned int>::nil())));
  return;
}

unsigned int
stmtest::stm_dequeue(const stm::TVar<std::shared_ptr<List<unsigned int>>> q) {
  std::shared_ptr<List<unsigned int>> xs = stm::readTVar(q);
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil) -> unsigned int {
            return stm::retry<unsigned int>();
          },
          [&](const typename List<unsigned int>::Cons _args) -> unsigned int {
            stm::writeTVar(q, _args.d_a1);
            return _args.d_a0;
          }},
      xs->v());
}

unsigned int
stmtest::stm_tryDequeue(const stm::TVar<std::shared_ptr<List<unsigned int>>> q,
                        const unsigned int dflt) {
  return stm::orElse<unsigned int>(stm_dequeue(q), dflt);
}

unsigned int stmtest::stm_queue_roundtrip(const unsigned int x) {
  stm::TVar<std::shared_ptr<List<unsigned int>>> q =
      stm::newTVar(List<unsigned int>::nil());
  stm_enqueue(q, x);
  return stm_dequeue(q);
}

unsigned int stmtest::io_queue_roundtrip(const unsigned int x) {
  return stm::atomically([&] { return stm_queue_roundtrip(x); });
}

unsigned int stmtest::stm_orElse_retry_example(const std::monostate) {
  stm::TVar<std::shared_ptr<List<unsigned int>>> q =
      stm::newTVar(List<unsigned int>::nil());
  return stm::orElse<unsigned int>(stm_dequeue(q), 42u);
}

unsigned int stmtest::io_orElse_retry_example() {
  return stm::atomically(
      [&] { return stm_orElse_retry_example(std::monostate{}); });
}
