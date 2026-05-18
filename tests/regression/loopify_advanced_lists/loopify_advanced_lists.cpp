#include "loopify_advanced_lists.h"

uint64_t LoopifyAdvancedLists::product(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified product: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.a0 * _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyAdvancedLists::compress(const List<uint64_t> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        *_write = std::make_unique<List<uint64_t>>(
            List<uint64_t>::cons(a0, List<uint64_t>::nil()));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        if (a0 == a00) {
          _loop_l = a1.get();
          continue;
        } else {
          auto _cell = std::make_unique<List<uint64_t>>(
              typename List<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_l = a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyAdvancedLists::pairwise_sum(const List<uint64_t> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons((a0 + a00), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = a10.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<std::pair<uint64_t, uint64_t>>
LoopifyAdvancedLists::group_pairs(const List<uint64_t> &l) {
  std::unique_ptr<List<std::pair<uint64_t, uint64_t>>> _head{};
  std::unique_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_unique<List<std::pair<uint64_t, uint64_t>>>(
          List<std::pair<uint64_t, uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        *_write = std::make_unique<List<std::pair<uint64_t, uint64_t>>>(
            List<std::pair<uint64_t, uint64_t>>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        auto _cell = std::make_unique<List<std::pair<uint64_t, uint64_t>>>(
            typename List<std::pair<uint64_t, uint64_t>>::Cons(
                std::make_pair(a0, a00), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                      (*_write)->v_mut())
                      .l;
        _loop_l = a10.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyAdvancedLists::interleave(List<uint64_t> l1,
                                                List<uint64_t> l2) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l2 = std::move(l2);
  List<uint64_t> _loop_l1 = std::move(l1);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(
            _loop_l1.v_mut())) {
      *_write = std::make_unique<List<uint64_t>>(std::move(_loop_l2));
      break;
    } else {
      auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1.v_mut());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l2.v_mut())) {
        *_write = std::make_unique<List<uint64_t>>(_loop_l1);
        break;
      } else {
        auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l2.v_mut());
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(std::move(a0), nullptr));
        auto _cell1 = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(std::move(a00), nullptr));
        std::get<typename List<uint64_t>::Cons>(_cell->v_mut()).l =
            std::move(_cell1);
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>(
                 std::get<typename List<uint64_t>::Cons>((*_write)->v_mut())
                     .l->v_mut())
                 .l;
        _loop_l2 = std::move(*a10);
        _loop_l1 = std::move(*a1);
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyAdvancedLists::concat_lists(
    const List<List<uint64_t>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<uint64_t>> *ll;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified concat_lists: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = _f.a0.app(_result);
    }
  }
  return _result;
}
