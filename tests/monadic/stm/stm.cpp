#include <stm.h>

#include <memory>
#include <mini_stm.h>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int stmtest::stm_basic_counter() {
  std::shared_ptr<stm::TVar<unsigned int>> c = stm::newTVar<unsigned int>(0u);
  c->write(1u);
  return c->read();
}

__attribute__((pure)) unsigned int stmtest::io_basic_counter() {
  return stm::atomically([&] { return stm_basic_counter(); });
}

__attribute__((pure)) unsigned int stmtest::stm_inc(const unsigned int x) {
  std::shared_ptr<stm::TVar<unsigned int>> c = stm::newTVar<unsigned int>(x);
  ::template modifyTVar<unsigned int>(c,
                                      [](unsigned int n) { return (n + 1); });
  return c->read();
}

__attribute__((pure)) unsigned int stmtest::io_inc(const unsigned int x) {
  return stm::atomically([&] { return stm_inc(x); });
}

__attribute__((pure)) unsigned int stmtest::stm_add_self(const unsigned int x) {
  std::shared_ptr<stm::TVar<unsigned int>> c = stm::newTVar<unsigned int>(x);
  unsigned int v = c->read();
  c->write((v + x));
  return c->read();
}

__attribute__((pure)) unsigned int stmtest::io_add_self(const unsigned int x) {
  return stm::atomically([&] { return stm_add_self(x); });
}

__attribute__((pure)) void stmtest::stm_enqueue(
    const std::shared_ptr<stm::TVar<std::shared_ptr<List<unsigned int>>>> q,
    const unsigned int x) {
  std::shared_ptr<List<unsigned int>> xs = q->read();
  return q->write(std::move(xs)->app(
      List<unsigned int>::cons(x, List<unsigned int>::nil())));
}

__attribute__((pure)) unsigned int stmtest::stm_dequeue(
    const std::shared_ptr<stm::TVar<std::shared_ptr<List<unsigned int>>>> q) {
  std::shared_ptr<List<unsigned int>> xs = q->read();
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args) -> unsigned int {
            return stm::retry<unsigned int>();
          },
          [&](const typename List<unsigned int>::Cons _args) -> unsigned int {
            q->write(_args.d_a1);
            return _args.d_a0;
          }},
      xs->v());
}

__attribute__((pure)) unsigned int stmtest::stm_tryDequeue(
    const std::shared_ptr<stm::TVar<std::shared_ptr<List<unsigned int>>>> q,
    const unsigned int dflt) {
  return stm::orElse<unsigned int>(stm_dequeue(q), dflt);
}

__attribute__((pure)) unsigned int
stmtest::stm_queue_roundtrip(const unsigned int x) {
  std::shared_ptr<stm::TVar<std::shared_ptr<List<unsigned int>>>> q =
      stm::newTVar<std::shared_ptr<List<unsigned int>>>(
          List<unsigned int>::nil());
  stm_enqueue(q, x);
  return stm_dequeue(q);
}

__attribute__((pure)) unsigned int
stmtest::io_queue_roundtrip(const unsigned int x) {
  return stm::atomically([&] { return stm_queue_roundtrip(x); });
}

__attribute__((pure)) unsigned int stmtest::stm_orElse_retry_example() {
  std::shared_ptr<stm::TVar<std::shared_ptr<List<unsigned int>>>> q =
      stm::newTVar<std::shared_ptr<List<unsigned int>>>(
          List<unsigned int>::nil());
  return stm::orElse<unsigned int>(stm_dequeue(q), 42u);
}

__attribute__((pure)) unsigned int stmtest::io_orElse_retry_example() {
  return stm::atomically([&] { return stm_orElse_retry_example(); });
}
