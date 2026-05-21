#include "loopify_scans.h"

List<uint64_t> LoopifyScans::scanl(uint64_t acc, const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(
          List<uint64_t>::cons(_loop_acc, List<uint64_t>::nil()));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(_loop_acc, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_l = a1.get();
      _loop_acc = (_loop_acc + a0);
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyScans::scanl_mult(uint64_t acc, const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(
          List<uint64_t>::cons(_loop_acc, List<uint64_t>::nil()));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(_loop_acc, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_l = a1.get();
      _loop_acc = (_loop_acc * a0);
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyScans::running_max(uint64_t current,
                                         const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_current = std::move(current);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(
          List<uint64_t>::cons(_loop_current, List<uint64_t>::nil()));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      uint64_t new_max;
      if (_loop_current < a0) {
        new_max = a0;
      } else {
        new_max = _loop_current;
      }
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(_loop_current, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_l = a1.get();
      _loop_current = new_max;
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyScans::running_min(uint64_t current,
                                         const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_current = std::move(current);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(
          List<uint64_t>::cons(_loop_current, List<uint64_t>::nil()));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      uint64_t new_min;
      if (a0 < _loop_current) {
        new_min = a0;
      } else {
        new_min = _loop_current;
      }
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(_loop_current, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_l = a1.get();
      _loop_current = new_min;
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyScans::pairwise_diff(uint64_t prev,
                                           const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_prev = std::move(prev);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      uint64_t diff;
      if (a0 < _loop_prev) {
        uint64_t sub =
            (((_loop_prev - a0) > _loop_prev ? 0 : (_loop_prev - a0)));
        if (_loop_prev < sub) {
          diff = UINT64_C(0);
        } else {
          diff = sub;
        }
      } else {
        uint64_t sub = (((a0 - _loop_prev) > a0 ? 0 : (a0 - _loop_prev)));
        if (a0 < sub) {
          diff = UINT64_C(0);
        } else {
          diff = sub;
        }
      }
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(diff, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_l = a1.get();
      _loop_prev = a0;
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyScans::accumulate_if_even(uint64_t acc,
                                                const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(
          List<uint64_t>::cons(_loop_acc, List<uint64_t>::nil()));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(0)) {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(_loop_acc, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = a1.get();
        _loop_acc = (_loop_acc + a0);
        continue;
      } else {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(_loop_acc, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}
