// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// ITree's rec and call in erased mode (theories/Monads/ITree.v).  rec body a
// runs body a, and answers each call event the body performs by running the
// body again: a call is a recursive call of the innermost rec whose calls
// take an A and return a B.  The handlers live on a stack per thread, so a
// rec is reentrant, and a call returns its result to the code after it.
//
// Calls are told apart by their types alone: a body that performs a call
// meant for an enclosing rec of the same A and B, from inside an inner one,
// reaches the inner one.

#pragma once

#include <functional>
#include <type_traits>
#include <utility>
#include <vector>

namespace crane {

template <class A, class B> std::vector<std::function<B(A)> *> &rec_handlers() {
  thread_local std::vector<std::function<B(A)> *> handlers;
  return handlers;
}

// A call of the innermost rec taking an A and returning a B.
template <class A, class B> B rec_call(A a) {
  return (*rec_handlers<A, B>().back())(std::move(a));
}

// The body run on a, with its calls answered by the body.
template <class A, class B, class F> B rec(F &&body, A a) {
  std::function<B(A)> self = [&body](A x) -> B {
    if constexpr (std::is_void_v<std::invoke_result_t<F &, A>>) {
      body(std::move(x));
      return B{};
    } else {
      return body(std::move(x));
    }
  };
  auto &handlers = rec_handlers<A, B>();
  handlers.push_back(&self);
  struct pop {
    std::vector<std::function<B(A)> *> &handlers;
    ~pop() { handlers.pop_back(); }
  } guard{handlers};
  return self(std::move(a));
}

} // namespace crane
