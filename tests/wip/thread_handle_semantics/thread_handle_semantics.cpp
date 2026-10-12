#include "thread_handle_semantics.h"

void ThreadHandleSemantics::work(uint64_t) { return; }

uint64_t ThreadHandleSemantics::never_joined(uint64_t n) {
  std::thread _x = std::thread(work, n);
  return n;
}

uint64_t ThreadHandleSemantics::joined_twice(uint64_t n) {
  std::thread t = std::thread(work, n);
  t.join();
  std::move(t).join();
  return n;
}

List<std::thread> ThreadHandleSemantics::spawn_all(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<std::thread>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    std::thread h = std::thread(work, a0);
    List<std::thread> hs = spawn_all(*a1);
    return List<std::thread>::cons(std::move(h), std::move(hs));
  }
}

void ThreadHandleSemantics::join_all(const List<std::thread> &l) {
  if (std::holds_alternative<typename List<std::thread>::Nil>(l.v())) {
    return;
  } else {
    const auto &[a0, a1] = std::get<typename List<std::thread>::Cons>(l.v());
    a0.join();
    join_all(*a1);
    return;
  }
}
