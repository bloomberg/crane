#include "typed_mapping_access.h"

/// Reads only: the canonical read form.
uint64_t TypedMappingAccess::peek(const access_support::handle &x0_) {
  return access_support::get(x0_);
}

/// Writes through the handle, two calls deep.
access_support::handle
TypedMappingAccess::poke(const access_support::handle &x0_, uint64_t x1_) {
  return access_support::set(x0_, x1_);
}

access_support::handle
TypedMappingAccess::poke_middle(const access_support::handle &h, uint64_t n) {
  return poke(h, (n + 1));
}

uint64_t TypedMappingAccess::poke_outer(const access_support::handle &h,
                                        uint64_t n) {
  return access_support::get(poke_middle(h, (n + 1)));
}

/// Reseats the handle, two calls deep.
uint64_t TypedMappingAccess::reseat(access_support::handle &h, uint64_t n) {
  return access_support::get(access_support::reseat(h, n));
}

uint64_t TypedMappingAccess::reseat_outer(access_support::handle &h,
                                          uint64_t n) {
  return (reseat(h, n) + 1);
}

/// Keeps the handle: owned, by value, even though it is reseated too.
access_support::handle TypedMappingAccess::keep(access_support::handle x0_) {
  return access_support::keep(std::move(x0_));
}

uint64_t TypedMappingAccess::keep_and_reseat(access_support::handle h) {
  access_support::handle k = access_support::keep(h);
  uint64_t r = access_support::get(access_support::reseat(h, UINT64_C(7)));
  return (access_support::get(k)) + r;
}

/// Writes the buffer in place, two calls deep.
uint64_t TypedMappingAccess::buf_size(const access_support::buf &x0_) {
  return access_support::buf_len(x0_);
}

access_support::buf TypedMappingAccess::push(access_support::buf &x0_,
                                             uint64_t x1_) {
  return access_support::buf_push(x0_, x1_);
}

access_support::buf TypedMappingAccess::push_middle(access_support::buf &b) {
  return push(b, UINT64_C(1));
}

uint64_t TypedMappingAccess::push_outer(access_support::buf &b) {
  return access_support::buf_len(push_middle(b));
}

/// A recursive group: ping reseats, pong only passes its handle to
/// ping, and is first in the group.
uint64_t TypedMappingAccess::pong(access_support::handle &h, uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (n <= 0) {
      return access_support::get(h);
    } else {
      uint64_t m = n - 1;
      if (m <= 0) {
        return access_support::get(access_support::reseat(h, UINT64_C(9)));
      } else {
        uint64_t m0 = m - 1;
        n = m0;
      }
    }
  }
}

uint64_t TypedMappingAccess::ping(access_support::handle &h, uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (n <= 0) {
      return access_support::get(access_support::reseat(h, UINT64_C(9)));
    } else {
      uint64_t m = n - 1;
      if (m <= 0) {
        return access_support::get(h);
      } else {
        uint64_t m0 = m - 1;
        n = m0;
      }
    }
  }
}

uint64_t TypedMappingAccess::reseat_value(access_support::handle h) {
  return access_support::get(access_support::reseat(h, UINT64_C(3)));
}

uint64_t TypedMappingAccess::through_value(const access_support::handle &h) {
  return apply_handle(reseat_value, h);
}

/// A value that is not a variable, passed where the callee replaces or
/// writes it in place, is materialised for the call.
uint64_t TypedMappingAccess::reseat_fresh(uint64_t n) {
  return reseat(crane::writable(access_support::make(n)).ref(), UINT64_C(4));
}

uint64_t TypedMappingAccess::reseat_fresh_op(uint64_t n) {
  return access_support::get(access_support::reseat(
      crane::writable(access_support::make(n)).ref(), UINT64_C(2)));
}

uint64_t TypedMappingAccess::push_fresh(uint64_t n) {
  return push_outer(crane::writable(access_support::buf_make(n)).ref());
}

/// Self recursion: in a loop, and through a stack of frames
/// (Crane Loopify is set).
uint64_t TypedMappingAccess::reseat_loop(access_support::handle &h,
                                         uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  access_support::handle &_loop_h = h;
  while (true) {
    if (n <= 0) {
      return access_support::get(_loop_h);
    } else {
      uint64_t m = n - 1;
      uint64_t _next_n = m;
      _loop_h = access_support::reseat(_loop_h, n);
      n = _next_n;
    }
  }
}

uint64_t TypedMappingAccess::push_loop(access_support::buf &b, uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  access_support::buf &_loop_b = b;
  while (true) {
    if (n <= 0) {
      return access_support::buf_len(_loop_b);
    } else {
      uint64_t m = n - 1;
      uint64_t _next_n = m;
      _loop_b = access_support::buf_push(_loop_b, n);
      n = _next_n;
    }
  }
}

uint64_t TypedMappingAccess::reseat_sum(access_support::handle &h, uint64_t n) {
  // Explicit stack replaces the non-tail recursion of reseat_sum: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_reseat_sum_in_S {
    uint64_t n;
  };

  using _frame = std::variant<_call, _after_reseat_sum_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = access_support::get(h);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_after_reseat_sum_in_S{n});
        _stack.emplace_back(_call{m});
      }
    } else {
      auto _f = std::move(std::get<_after_reseat_sum_in_S>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      auto _once1 = access_support::get(access_support::reseat(h, n));
      auto _once2 = _result;
      _result = _once1 + std::move(_once2);
    }
  }
  return _result;
}

uint64_t TypedMappingAccess::reseat_each(access_support::handle &h,
                                         const List<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_loop_l = &l;
  access_support::handle &_loop_h = h;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return access_support::get(_loop_h);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      _loop_l = crane_raw(a1);
      _loop_h = access_support::reseat(_loop_h, a0);
    }
  }
}

uint64_t TypedMappingAccess::push_each(access_support::buf &b,
                                       const List<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_loop_l = &l;
  access_support::buf &_loop_b = b;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return access_support::buf_len(_loop_b);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      _loop_l = crane_raw(a1);
      _loop_b = access_support::buf_push(_loop_b, a0);
    }
  }
}

List<uint64_t> TypedMappingAccess::push_all(access_support::buf &b,
                                            const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto _cell = typename List<uint64_t>::Cons(
          access_support::buf_len(access_support::buf_push(b, a0)), nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_l = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t TypedMappingAccess::reseat_down(access_support::handle &h,
                                         const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of reseat_down: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
    access_support::handle h;
  };

  struct _after_reseat_down_in_Cons {};

  using _frame = std::variant<_call, _after_reseat_down_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l, h});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      access_support::handle h = std::move(_f.h);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = access_support::get(h);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_reseat_down_in_Cons{});
        _stack.emplace_back(_call{crane_raw(a1),
                                  access_support::reseat(h, a0)});
      }
    } else {
      auto _f = std::move(std::get<_after_reseat_down_in_Cons>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    }
  }
  return _result;
}

/// In a closure: the lambda's own parameter, and a captured one.
List<uint64_t>
TypedMappingAccess::reseat_each_value(const List<access_support::handle> &l) {
  return l.template map<uint64_t>([](const access_support::handle &h) {
    return access_support::get(
        access_support::reseat(crane::writable(h).ref(), UINT64_C(1)));
  });
}

List<uint64_t>
TypedMappingAccess::reseat_captured(const access_support::handle &h,
                                    const List<uint64_t> &l) {
  return l.template map<uint64_t>([=](uint64_t x) {
    return access_support::get(
        access_support::reseat(crane::writable(h).ref(), x));
  });
}
