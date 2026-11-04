#include "boxed_element_container_cast.h"

/// A container cast into a callee generic over the element, over a list
/// mapped with a Boxed Element wrapper.
///
/// val recurses through list, so list (string * val) is
/// crane::list<crane::box<std::pair<std::string, Val>>> wherever it is
/// written.  The predicate below hands an erased list (string * val) to
/// nodupKeys, a function template over list (string * A) whose own
/// declaration never boxes its element (a bare type variable never recurses).
/// The cast that recovers the argument must therefore name the element
/// unboxed, as the declaration does, or template argument deduction fails;
/// the action hands the same leaf to VAssoc's concrete factory, whose cast
/// keeps the box.  run_entry and action_size run both.
BoxedElementContainerCast::nt_semty
BoxedElementContainerCast::sample_nt(BoxedElementContainerCast::Nonterminal x) {
  switch (x) {
  case Nonterminal::VALUE: {
    return val::vnull();
  }
  case Nonterminal::OBJ: {
    return crane::cons(
        std::make_pair(
            crane::obj(
                std::string(
                    1, (static_cast<char>(
                           (true ? 1 : 0) | (true ? 2 : 0) | (false ? 4 : 0) |
                           (true ? 8 : 0) | (false ? 16 : 0) | (true ? 32 : 0) |
                           (true ? 64 : 0) | (false ? 128 : 0)))) +
                std::string()),
            crane::obj(val::vnull())),
        crane::cons(
            std::make_pair(
                crane::obj(std::string(
                               1, (static_cast<char>(
                                      (false ? 1 : 0) | (false ? 2 : 0) |
                                      (true ? 4 : 0) | (true ? 8 : 0) |
                                      (false ? 16 : 0) | (true ? 32 : 0) |
                                      (true ? 64 : 0) | (false ? 128 : 0)))) +
                           std::string()),
                crane::obj(val::vnull())),
            crane::list<crane::obj>{}));
  }
  default:
    std::unreachable();
  }
}

BoxedElementContainerCast::symbol_semty
BoxedElementContainerCast::sample_symbol(
    const BoxedElementContainerCast::symbol &s) {
  if (std::holds_alternative<typename BoxedElementContainerCast::symbol::T>(
          s.v())) {
    return sample_t;
  } else {
    const auto &[a0] =
        std::get<typename BoxedElementContainerCast::symbol::NT>(s.v());
    return sample_nt(a0);
  }
}

BoxedElementContainerCast::symbols_semty
BoxedElementContainerCast::sample_symbols(
    const crane::list<BoxedElementContainerCast::symbol> &ys) {
  if (ys.empty()) {
    return std::monostate{};
  } else {
    const BoxedElementContainerCast::symbol &y = ys.front();
    auto ys_ = ys.tail();
    return std::make_pair(crane::obj(sample_symbol(y)),
                          crane::obj(sample_symbols(ys_)));
  }
}

bool BoxedElementContainerCast::run_entry(
    const SigT<std::pair<BoxedElementContainerCast::Nonterminal,
                         crane::list<BoxedElementContainerCast::symbol>>,
               std::pair<crane::obj, crane::obj>> &e) {
  const auto &[x0, a1] = e;
  const auto &[_x, ys] = x0;
  const auto &[pr, _x0] = a1;
  return crane::any_cast<bool>(
      crane::any_cast<crane::fn<crane::obj(crane::obj)>>(pr)(
          sample_symbols(ys)));
}

uint64_t
BoxedElementContainerCast::size_of(BoxedElementContainerCast::Nonterminal x,
                                   BoxedElementContainerCast::nt_semty v) {
  switch (x) {
  case Nonterminal::VALUE: {
    auto &&_sv = crane::any_cast<BoxedElementContainerCast::val>(std::move(v));
    if (std::holds_alternative<typename BoxedElementContainerCast::val::VAssoc>(
            _sv.v_mut())) {
      auto &[a0] = std::get<typename BoxedElementContainerCast::val::VAssoc>(
          _sv.v_mut());
      return Datatypes::template length<
          std::pair<std::string, BoxedElementContainerCast::val>>(
          std::move(a0));
    } else if (std::holds_alternative<
                   typename BoxedElementContainerCast::val::VStr>(
                   _sv.v_mut())) {
      return UINT64_C(100);
    } else {
      return UINT64_C(0);
    }
    break;
  }
  case Nonterminal::OBJ: {
    return Datatypes::template length<
        std::pair<std::string, BoxedElementContainerCast::val>>(
        crane_container_cast<crane::list<
            std::pair<std::string, BoxedElementContainerCast::val>>>(
            crane::any_cast<crane::list<crane::obj>>(std::move(v))));
  }
  default:
    std::unreachable();
  }
}

uint64_t BoxedElementContainerCast::action_size(
    const SigT<std::pair<BoxedElementContainerCast::Nonterminal,
                         crane::list<BoxedElementContainerCast::symbol>>,
               std::pair<crane::obj, crane::obj>> &e) {
  const auto &[x, a1] = e;
  const auto &[x1, ys] = x;
  const auto &[_x, act] = a1;
  return size_of(x1, crane::any_cast<crane::fn<crane::obj(crane::obj)>>(act)(
                         sample_symbols(ys)));
}
