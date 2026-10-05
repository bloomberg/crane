#include "loopify_advanced_lists.h"

uint64_t LoopifyAdvancedLists::product(
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified product: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      _result = (a0 * std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyAdvancedLists::compress(const List<uint64_t> &l) {
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
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        auto _value = List<uint64_t>::cons(a0, List<uint64_t>::nil());
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        if (a0 == a00) {
          _loop_l = crane_raw(a1);
          continue;
        } else {
          auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyAdvancedLists::pairwise_sum(const List<uint64_t> &l) {
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
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        auto _cell = typename List<uint64_t>::Cons((a0 + a00), nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a10);
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<std::pair<uint64_t, uint64_t>>
LoopifyAdvancedLists::group_pairs(const List<uint64_t> &l) {
  std::optional<List<std::pair<uint64_t, uint64_t>>> _root{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
      (_write
           ? *(*_write = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                   std::move(_value)))
           : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
        auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                            std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_sv0.v());
        auto _cell = typename List<std::pair<uint64_t, uint64_t>>::Cons(
            std::make_pair(a0, a00), nullptr);
        List<std::pair<uint64_t, uint64_t>> &_node =
            (_write
                 ? *(*_write =
                         std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                             std::move(_cell)))
                 : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                      _node.v_mut())
                      .l;
        _loop_l = crane_raw(a10);
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyAdvancedLists::interleave(List<uint64_t> l1,
                                                List<uint64_t> l2) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  List<uint64_t> _loop_l2 = std::move(l2);
  List<uint64_t> _loop_l1 = std::move(l1);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(
            _loop_l1.v_mut())) {
      auto _value = std::move(_loop_l2);
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1.v_mut());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l2.v_mut())) {
        auto _value = _loop_l1;
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l2.v_mut());
        auto _cell1 = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(std::move(a00), nullptr));
        auto _cell = typename List<uint64_t>::Cons(a0, std::move(_cell1));
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(
                      std::get<typename List<uint64_t>::Cons>(_node.v_mut())
                          .l->v_mut())
                      .l;
        _loop_l2 = List<uint64_t>(*a10);
        _loop_l1 = List<uint64_t>(*a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyAdvancedLists::concat_lists(
    const List<List<uint64_t>> &ll) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

  struct CraneEnter {
    const List<List<uint64_t>> *ll;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    List<uint64_t> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&ll});
  /// Loopified concat_lists: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      List<uint64_t> a0 = std::move(_f.a0);
      _result = a0.app(std::move(_result));
    }
  }
  return _result;
}
