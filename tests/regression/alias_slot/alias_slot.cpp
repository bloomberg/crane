#include "alias_slot.h"

AliasSlot::parts AliasSlot::expr_parts(const AliasSlot::expr &e,
                                       const List<String> &k) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto k_1 = crane::immortal(String::string0(
      Ascii::ascii0(true, true, false, true, false, true, false, false),
      String::emptystring()));
  static const auto k_2 = crane::immortal(String::string0(
      Ascii::ascii0(true, false, false, true, false, true, false, false),
      String::emptystring()));
  static const auto k_3 = crane::immortal(String::string0(
      Ascii::ascii0(false, false, false, true, false, true, false, false),
      String::emptystring()));

  // Explicit stack replaces the non-tail recursion of expr_parts: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    List<String> k;
    const AliasSlot::expr *e;
  };

  struct _after_expr_parts_in_EAdd {
    const AliasSlot::expr *a0;
  };

  struct _after_expr_parts_in_EAdd_2 {};

  using _frame = std::variant<_call, _after_expr_parts_in_EAdd,
                              _after_expr_parts_in_EAdd_2>;
  AliasSlot::parts _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{k, &e});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (crane::holds_alternative<_call>(_popped)) {
      auto _f = std::move(crane::get<_call>(_popped));
      _stack.pop_back();
      List<String> k = std::move(_f.k);
      const AliasSlot::expr &e = *_f.e;
      if (crane::holds_alternative<typename AliasSlot::expr::ELit>(e.v())) {
        const auto &[s0] = crane::get<typename AliasSlot::expr::ELit>(e.v());
        _result = List<String>::cons(s0, std::move(k));
      } else {
        const auto &[a0, b0] =
            crane::get<typename AliasSlot::expr::EAdd>(e.v());
        _stack.emplace_back(_after_expr_parts_in_EAdd{crane_raw(a0)});
        _stack.emplace_back(_call{std::move(k), crane_raw(b0)});
      }
    } else if (crane::holds_alternative<_after_expr_parts_in_EAdd>(_popped)) {
      auto _f = std::move(crane::get<_after_expr_parts_in_EAdd>(_popped));
      _stack.pop_back();
      const AliasSlot::expr &a0 = *_f.a0;
      List<String> rest = List<String>::cons(k_1, std::move(_result));
      if (crane::holds_alternative<typename AliasSlot::expr::ELit>(a0.v())) {
        _stack.emplace_back(_call{std::move(rest), &a0});
      } else {
        _stack.emplace_back(_after_expr_parts_in_EAdd_2{});
        _stack.emplace_back(
            _call{List<String>::cons(k_2, std::move(rest)), &a0});
      }
    } else {
      auto _f = std::move(crane::get<_after_expr_parts_in_EAdd_2>(_popped));
      _stack.pop_back();
      _result = List<String>::cons(k_3, std::move(_result));
    }
  }
  return _result;
}

/// Each of xs with a comma after it, then k: a loop that fills the
/// tail of the cell before, a cell whose type is the alias.
AliasSlot::parts AliasSlot::comma_parts(const List<String> &xs,
                                        List<String> k) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto k_1 = crane::immortal(String::string0(
      Ascii::ascii0(false, false, true, true, false, true, false, false),
      String::emptystring()));
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<AliasSlot::parts> _root{};
  crane::shared_box<AliasSlot::parts> *_write = nullptr;
  const List<String> *_loop_xs = &xs;
  while (true) {
    if (crane::holds_alternative<typename List<String>::Nil>(_loop_xs->v())) {
      auto _value = std::move(k);
      (_write ? *(*_write = crane::shared_box<AliasSlot::parts>::make(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          crane::get<typename List<String>::Cons>(_loop_xs->v());
      auto _cell = typename List<String>::Cons(
          a0, crane::shared_box<List<String>>::make(
                  typename List<String>::Cons(k_1, nullptr)));
      AliasSlot::parts &_node =
          (_write ? *(*_write = crane::shared_box<AliasSlot::parts>::make(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &crane::get<typename List<String>::Cons>(
              crane::get<typename List<String>::Cons>(_node.v_mut()).l->v_mut())
              .l;
      _loop_xs = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

AliasSlot::line AliasSlot::line_of(const AliasSlot::expr &e) {
  return line{UINT64_C(2), expr_parts(e, List<String>::nil())};
}

uint64_t AliasSlot::count(const AliasSlot::expr &e) {
  return line_of(e).l_text.length();
}
