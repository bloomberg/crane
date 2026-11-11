#include "alias_slot.h"

AliasSlot::parts AliasSlot::expr_parts(const AliasSlot::expr &e,
                                       const List<String> &k) {
  static const auto k_1 = crane::immortal(String::string0(
      Ascii::ascii0(true, true, false, true, false, true, false, false),
      String::emptystring()));
  static const auto k_2 = crane::immortal(String::string0(
      Ascii::ascii0(true, false, false, true, false, true, false, false),
      String::emptystring()));
  static const auto k_3 = crane::immortal(String::string0(
      Ascii::ascii0(false, false, false, true, false, true, false, false),
      String::emptystring()));

  /// CraneEnter: captures varying parameters for each recursive call.
  struct CraneEnter {
    List<String> k;
    const AliasSlot::expr *e;
  };

  /// CraneCont_EAdd: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_EAdd {
    const AliasSlot::expr *a0;
  };

  /// CraneCont_EAdd_1: resumes after recursive call, then processes rest.
  struct CraneCont_EAdd_1 {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_EAdd, CraneCont_EAdd_1>;
  AliasSlot::parts _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{k, &e});
  /// Loopified expr_parts: CraneEnter -> CraneCont_EAdd -> CraneCont_EAdd_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (crane::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(crane::get<CraneEnter>(_frame));
      const List<String> &k = _f.k;
      const AliasSlot::expr &e = *_f.e;
      if (crane::holds_alternative<typename AliasSlot::expr::ELit>(e.v())) {
        const auto &[s0] = crane::get<typename AliasSlot::expr::ELit>(e.v());
        _result = List<String>::cons(s0, k);
      } else {
        const auto &[a0, b0] =
            crane::get<typename AliasSlot::expr::EAdd>(e.v());
        _stack.emplace_back(CraneCont_EAdd{crane_raw(a0)});
        _stack.emplace_back(CraneEnter{k, crane_raw(b0)});
      }
    } else if (crane::holds_alternative<CraneCont_EAdd>(_frame)) {
      auto _f = std::move(crane::get<CraneCont_EAdd>(_frame));
      const AliasSlot::expr &a0 = *_f.a0;
      List<String> rest = List<String>::cons(k_1, std::move(_result));
      if (crane::holds_alternative<typename AliasSlot::expr::ELit>(a0.v())) {
        _stack.emplace_back(CraneEnter{std::move(rest), &a0});
      } else {
        _stack.emplace_back(CraneCont_EAdd_1{});
        _stack.emplace_back(
            CraneEnter{List<String>::cons(k_2, std::move(rest)), &a0});
      }
    } else {
      auto _f = std::move(crane::get<CraneCont_EAdd_1>(_frame));
      _result = List<String>::cons(k_3, std::move(_result));
    }
  }
  return _result;
}

/// Each of xs with a comma after it, then k: a loop that fills the
/// tail of the cell before, a cell whose type is the alias.
AliasSlot::parts AliasSlot::comma_parts(const List<String> &xs,
                                        List<String> k) {
  static const auto k_1 = crane::immortal(String::string0(
      Ascii::ascii0(false, false, true, true, false, true, false, false),
      String::emptystring()));
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
      auto _cell1 = crane::shared_box<List<String>>::make(
          typename List<String>::Cons(k_1, nullptr));
      auto _cell = typename List<String>::Cons(a0, std::move(_cell1));
      AliasSlot::parts &_node =
          (_write ? *(*_write = crane::shared_box<AliasSlot::parts>::make(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &crane::get<typename List<String>::Cons>(
                    crane::get<typename List<String>::Cons>(_node.v_mut())
                        .l->v_mut())
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
