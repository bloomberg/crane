#include <algorithm>
#include <any>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <mini_stm.h>
#include <optional>
#include <stm.h>
#include <string>
#include <utility>
#include <variant>
#include <vector>

unsigned int stmtest::stm_basic_counter() {
  std::shared_ptr<stm::TVar<unsigned int>> c = stm::newTVar<unsigned int>(0);
  stm::writeTVar<unsigned int>(c, (0 + 1));
  return stm::readTVar<unsigned int>(c);
}

unsigned int stmtest::io_basic_counter() {
  return stm::atomically([&] { return stm_basic_counter(); });
}

unsigned int stmtest::stm_inc(const unsigned int x) {
  std::shared_ptr<stm::TVar<unsigned int>> c = stm::newTVar<unsigned int>(x);
  ::modifyTVar<unsigned int>(c, [](unsigned int n) { return (n + 1); });
  return stm::readTVar<unsigned int>(c);
}

unsigned int stmtest::io_inc(const unsigned int x) {
  return stm::atomically([&] { return stm_inc(x); });
}

unsigned int stmtest::stm_add_self(const unsigned int x) {
  std::shared_ptr<stm::TVar<unsigned int>> c = stm::newTVar<unsigned int>(x);
  unsigned int v = stm::readTVar<unsigned int>(c);
  stm::writeTVar<unsigned int>(c, (v + x));
  return stm::readTVar<unsigned int>(c);
}

unsigned int stmtest::io_add_self(const unsigned int x) {
  return stm::atomically([&] { return stm_add_self(x); });
}

void stmtest::stm_enqueue(
    const std::shared_ptr<stm::TVar<std::shared_ptr<List::list<unsigned int>>>>
        q,
    const unsigned int x) {
  std::shared_ptr<List::list<unsigned int>> xs =
      stm::readTVar<std::shared_ptr<List::list<unsigned int>>>(q);
  return stm::writeTVar<std::shared_ptr<List::list<unsigned int>>>(
      q,
      ::app<unsigned int>(xs, List::list<unsigned int>::ctor::cons_(
                                  x, List::list<unsigned int>::ctor::nil_())));
}

unsigned int stmtest::stm_dequeue(
    const std::shared_ptr<stm::TVar<std::shared_ptr<List::list<unsigned int>>>>
        q) {
  std::shared_ptr<List::list<unsigned int>> xs =
      stm::readTVar<std::shared_ptr<List::list<unsigned int>>>(q);
  return std::visit(
      Overloaded{[](const typename List::list<unsigned int>::nil _args)
                     -> unsigned int { return stm::retry<unsigned int>(); },
                 [&](const typename List::list<unsigned int>::cons _args)
                     -> unsigned int {
                   unsigned int y = _args._a0;
                   std::shared_ptr<List::list<unsigned int>> ys = _args._a1;
                   stm::writeTVar<std::shared_ptr<List::list<unsigned int>>>(
                       q, ys);
                   return y;
                 }},
      xs->v());
}

unsigned int stmtest::stm_tryDequeue(
    const std::shared_ptr<stm::TVar<std::shared_ptr<List::list<unsigned int>>>>
        q,
    const unsigned int dflt) {
  return stm::orElse<unsigned int>(stm_dequeue(q), dflt);
}

unsigned int stmtest::stm_queue_roundtrip(const unsigned int x) {
  std::shared_ptr<stm::TVar<std::shared_ptr<List::list<unsigned int>>>> q =
      stm::newTVar<std::shared_ptr<List::list<unsigned int>>>(
          List::list<unsigned int>::ctor::nil_());
  stm_enqueue(q, x);
  return stm_dequeue(q);
}

unsigned int stmtest::io_queue_roundtrip(const unsigned int x) {
  return stm::atomically([&] { return stm_queue_roundtrip(x); });
}

unsigned int stmtest::stm_orElse_retry_example() {
  std::shared_ptr<stm::TVar<std::shared_ptr<List::list<unsigned int>>>> q =
      stm::newTVar<std::shared_ptr<List::list<unsigned int>>>(
          List::list<unsigned int>::ctor::nil_());
  return stm::orElse<unsigned int>(
      stm_dequeue(q),
      ((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) +
                                           1) +
                                          1) +
                                         1) +
                                        1) +
                                       1) +
                                      1) +
                                     1) +
                                    1) +
                                   1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

unsigned int stmtest::io_orElse_retry_example() {
  return stm::atomically([&] { return stm_orElse_retry_example(); });
}
