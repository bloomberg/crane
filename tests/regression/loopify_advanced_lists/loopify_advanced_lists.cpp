#include <loopify_advanced_lists.h>

unsigned int LoopifyAdvancedLists::product(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Resume_Cons: saves [d_a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Loopified product: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 1u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.d_a0 * _result);
    }
  }
  return _result;
}

List<unsigned int> LoopifyAdvancedLists::compress(const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(d_a0, List<unsigned int>::nil()));
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        if (d_a0 == d_a00) {
          _loop_l = d_a1.get();
          continue;
        } else {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = d_a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int>
LoopifyAdvancedLists::pairwise_sum(const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons((d_a0 + d_a00), nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = d_a10.get();
        continue;
      }
    }
  }
  return std::move(*(_head));
}

List<std::pair<unsigned int, unsigned int>>
LoopifyAdvancedLists::group_pairs(const List<unsigned int> &l) {
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *(_write) = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
          List<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
        *(_write) =
            std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                List<std::pair<unsigned int, unsigned int>>::nil());
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_sv0.v());
        auto _cell =
            std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                typename List<std::pair<unsigned int, unsigned int>>::Cons(
                    std::make_pair(d_a0, d_a00), nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<
                 typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                 (*_write)->v_mut())
                 .d_a1;
        _loop_l = d_a10.get();
        continue;
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifyAdvancedLists::interleave(List<unsigned int> l1,
                                                    List<unsigned int> l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l2 = std::move(l2);
  List<unsigned int> _loop_l1 = std::move(l1);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1.v_mut())) {
      *(_write) = std::make_unique<List<unsigned int>>(std::move(_loop_l2));
      break;
    } else {
      auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1.v_mut());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2.v_mut())) {
        *(_write) = std::make_unique<List<unsigned int>>(_loop_l1);
        break;
      } else {
        auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2.v_mut());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        auto _cell1 = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a00, nullptr));
        std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1 =
            std::move(_cell1);
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>(
                 std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1->v_mut())
                 .d_a1;
        _loop_l2 = std::move(*(d_a10));
        _loop_l1 = std::move(*(d_a1));
        continue;
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifyAdvancedLists::concat_lists(
    const List<List<unsigned int>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<unsigned int>> *ll;
  };

  /// _Resume_Cons: saves [d_a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<unsigned int> d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified concat_lists: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<unsigned int>> &ll = *(_f.ll);
      if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
              ll.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<List<unsigned int>>::Cons>(ll.v());
        _stack.emplace_back(_Resume_Cons{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = _f.d_a0.app(_result);
    }
  }
  return _result;
}
