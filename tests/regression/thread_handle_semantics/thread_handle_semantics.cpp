#include "thread_handle_semantics.h"

void ThreadHandleSemantics::work(uint64_t) {}

uint64_t ThreadHandleSemantics::never_joined(uint64_t n) {
  std::shared_future<void> _x =
      std::async(
          std::launch::async,
          [](auto f, auto a) { f(std::move(a)); },
          work,
          n)
          .share();
  return n;
}

uint64_t ThreadHandleSemantics::joined_twice(uint64_t n) {
  std::shared_future<void> t =
      std::async(
          std::launch::async,
          [](auto f, auto a) { f(std::move(a)); },
          work,
          n)
          .share();
  t.wait();
  std::move(t).wait();
  return n;
}

List<std::shared_future<void>>
ThreadHandleSemantics::spawn_all(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<std::shared_future<void>>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    std::shared_future<void> h =
        std::async(
            std::launch::async,
            [](auto f, auto a) { f(std::move(a)); },
            work,
            a0)
            .share();
    return List<std::shared_future<void>>::cons(std::move(h), spawn_all(*a1));
  }
}

void ThreadHandleSemantics::join_all(const List<std::shared_future<void>> &l) {
  if (std::holds_alternative<typename List<std::shared_future<void>>::Nil>(
          l.v())) {
    return;
  } else {
    const auto &[a0, a1] =
        std::get<typename List<std::shared_future<void>>::Cons>(l.v());
    a0.wait();
    join_all(*a1);
  }
}
