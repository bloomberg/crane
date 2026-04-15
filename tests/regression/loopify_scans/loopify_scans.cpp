#include <loopify_scans.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
LoopifyScans::scanl(const unsigned int acc,
                    const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::cons(_loop_acc, List<unsigned int>::nil());
      } else {
        _head = List<unsigned int>::cons(_loop_acc, List<unsigned int>::nil());
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto _cell = List<unsigned int>::cons(_loop_acc, nullptr);
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      std::shared_ptr<List<unsigned int>> _next_l = d_a1;
      unsigned int _next_acc = (_loop_acc + d_a0);
      _loop_l = std::move(_next_l);
      _loop_acc = std::move(_next_acc);
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyScans::scanl_mult(const unsigned int acc,
                         const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::cons(_loop_acc, List<unsigned int>::nil());
      } else {
        _head = List<unsigned int>::cons(_loop_acc, List<unsigned int>::nil());
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto _cell = List<unsigned int>::cons(_loop_acc, nullptr);
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      std::shared_ptr<List<unsigned int>> _next_l = d_a1;
      unsigned int _next_acc = (_loop_acc * d_a0);
      _loop_l = std::move(_next_l);
      _loop_acc = std::move(_next_acc);
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyScans::running_max(const unsigned int current,
                          const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_current = current;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::cons(_loop_current, List<unsigned int>::nil());
      } else {
        _head =
            List<unsigned int>::cons(_loop_current, List<unsigned int>::nil());
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      unsigned int new_max;
      if (_loop_current < d_a0) {
        new_max = d_a0;
      } else {
        new_max = _loop_current;
      }
      auto _cell = List<unsigned int>::cons(_loop_current, nullptr);
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      std::shared_ptr<List<unsigned int>> _next_l = d_a1;
      unsigned int _next_current = new_max;
      _loop_l = std::move(_next_l);
      _loop_current = std::move(_next_current);
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyScans::running_min(const unsigned int current,
                          const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_current = current;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::cons(_loop_current, List<unsigned int>::nil());
      } else {
        _head =
            List<unsigned int>::cons(_loop_current, List<unsigned int>::nil());
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      unsigned int new_min;
      if (d_a0 < _loop_current) {
        new_min = d_a0;
      } else {
        new_min = _loop_current;
      }
      auto _cell = List<unsigned int>::cons(_loop_current, nullptr);
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      std::shared_ptr<List<unsigned int>> _next_l = d_a1;
      unsigned int _next_current = new_min;
      _loop_l = std::move(_next_l);
      _loop_current = std::move(_next_current);
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyScans::pairwise_diff(const unsigned int prev,
                            const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_prev = prev;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      unsigned int diff;
      if (d_a0 < _loop_prev) {
        unsigned int sub =
            (((_loop_prev - d_a0) > _loop_prev ? 0 : (_loop_prev - d_a0)));
        if (_loop_prev < sub) {
          diff = 0u;
        } else {
          diff = sub;
        }
      } else {
        unsigned int sub =
            (((d_a0 - _loop_prev) > d_a0 ? 0 : (d_a0 - _loop_prev)));
        if (d_a0 < sub) {
          diff = 0u;
        } else {
          diff = sub;
        }
      }
      auto _cell = List<unsigned int>::cons(diff, nullptr);
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      std::shared_ptr<List<unsigned int>> _next_l = d_a1;
      unsigned int _next_prev = d_a0;
      _loop_l = std::move(_next_l);
      _loop_prev = std::move(_next_prev);
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyScans::accumulate_if_even(const unsigned int acc,
                                 const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::cons(_loop_acc, List<unsigned int>::nil());
      } else {
        _head = List<unsigned int>::cons(_loop_acc, List<unsigned int>::nil());
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if ((2u ? d_a0 % 2u : d_a0) == 0u) {
        auto _cell = List<unsigned int>::cons(_loop_acc, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        std::shared_ptr<List<unsigned int>> _next_l = d_a1;
        unsigned int _next_acc = (_loop_acc + d_a0);
        _loop_l = std::move(_next_l);
        _loop_acc = std::move(_next_acc);
        continue;
      } else {
        auto _cell = List<unsigned int>::cons(_loop_acc, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_l = d_a1;
        continue;
      }
    }
  }
  return _head;
}
