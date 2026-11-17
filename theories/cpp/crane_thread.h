// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// crane::thread: Rocq's [thread], a value like any other.  A Rocq program may
// copy a thread handle, keep it in a list, join it twice or never; a
// std::thread does none of that, being move-only, joinable once, and fatal to
// destroy unjoined.  A crane::thread is a handle on one shared state: every
// copy joins the same thread, the first join waits for it and the rest return
// at once, and the last copy to go joins a thread no one did.

#ifndef INCLUDED_CRANE_THREAD
#define INCLUDED_CRANE_THREAD

#include <memory>
#include <mutex>
#include <thread>
#include <utility>

namespace crane {

class thread {
  struct state {
    std::thread t;
    std::once_flag joined;

    void join() {
      std::call_once(joined, [this] { t.join(); });
    }
    ~state() { join(); }
  };

  std::shared_ptr<state> s_;

public:
  template <class F, class... A>
  explicit thread(F &&f, A &&...a) : s_(std::make_shared<state>()) {
    s_->t = std::thread(std::forward<F>(f), std::forward<A>(a)...);
  }

  void join() const { s_->join(); }
};

} // namespace crane

#endif // INCLUDED_CRANE_THREAD
