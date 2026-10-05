#include "loopify_list_access.h"

uint64_t LoopifyListAccess::nth(uint64_t n, const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (_loop_n == UINT64_C(0)) {
        return a0;
      } else {
        _loop_l = crane_raw(a1);
        _loop_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
      }
    }
  }
}

uint64_t LoopifyListAccess::last(const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
        return a0;
      } else {
        _loop_l = crane_raw(a1);
      }
    }
  }
}

uint64_t LoopifyListAccess::index_of_aux(uint64_t x, const List<uint64_t> &l,
                                         uint64_t idx) {
  uint64_t _loop_idx = std::move(idx);
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        return _loop_idx;
      } else {
        _loop_idx = (_loop_idx + UINT64_C(1));
        _loop_l = crane_raw(a1);
      }
    }
  }
}

uint64_t LoopifyListAccess::index_of(uint64_t x, const List<uint64_t> &l) {
  return index_of_aux(x, l, UINT64_C(0));
}

bool LoopifyListAccess::member(uint64_t x, const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return false;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        return true;
      } else {
        _loop_l = crane_raw(a1);
      }
    }
  }
}

uint64_t
LoopifyListAccess::lookup(uint64_t key,
                          const List<std::pair<uint64_t, uint64_t>> &l) {
  const List<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename List<std::pair<uint64_t, uint64_t>>::Nil>(_loop_l->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
              _loop_l->v());
      const auto &[k, v] = a0;
      if (k == key) {
        return v;
      } else {
        _loop_l = crane_raw(a1);
      }
    }
  }
}

List<uint64_t>
LoopifyListAccess::lookup_all(uint64_t key,
                              const List<std::pair<uint64_t, uint64_t>> &l) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename List<std::pair<uint64_t, uint64_t>>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
              _loop_l->v());
      const auto &[k, v] = a0;
      if (k == key) {
        auto _cell = typename List<uint64_t>::Cons(v, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      } else {
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

uint64_t LoopifyListAccess::count(
    uint64_t x,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont1: resumes after recursive call, then processes rest.
  struct CraneCont1 {};

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified count: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if (x == a0) {
          _stack.emplace_back(CraneCont1{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      _result = (UINT64_C(1) + std::move(_result));
    }
  }
  return _result;
}

bool LoopifyListAccess::elem_at_eq(uint64_t idx, uint64_t val,
                                   const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_idx = std::move(idx);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return false;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (_loop_idx == UINT64_C(0)) {
        return a0 == val;
      } else {
        _loop_l = crane_raw(a1);
        _loop_idx = (((_loop_idx - UINT64_C(1)) > _loop_idx
                          ? 0
                          : (_loop_idx - UINT64_C(1))));
      }
    }
  }
}

uint64_t LoopifyListAccess::nth_default(uint64_t n, uint64_t default0,
                                        const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return default0;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (_loop_n == UINT64_C(0)) {
        return a0;
      } else {
        _loop_l = crane_raw(a1);
        _loop_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
      }
    }
  }
}
