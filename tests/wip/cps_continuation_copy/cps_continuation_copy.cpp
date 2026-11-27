#include "cps_continuation_copy.h"

/// sumk is tail recursive and is loopified into a for, so it should run in
/// constant stack.  It did not: the continuation parameter k was a
/// std::function taken by value and then *copied* into the next
/// continuation's capture, rather than moved out of the dying parameter.  Each
/// iteration therefore copied the whole chain, and copying a chain of a
/// hundred thousand nested std::functions recursed a hundred thousand deep
/// and overflowed the stack.
///
/// Diagnosis (2026-11-24): that defect is gone.  A continuation is a shared,
/// immutable crane::fn, so the copy is a reference-count increment, and
/// sumk loopifies (the test was missing Set Crane Loopify, which it
/// needs to be about the loop at all; List.seq then builds its list in a
/// loop too).  Destroying the chain is iterative as well.  What still
/// overflows, at the suite's -O0, is calling the chain: _loop_k(0)
/// runs a hundred thousand closures, each tail-calling the next
/// (fun s => k (x + s)).  OCaml eliminates those tail calls; C++ does not
/// promise to, and at -O0 each level costs some 200 bytes of stack
/// through crane::fn's invocation thunk, so about 40000 levels exhaust
/// the default 8 MB stack.  The same program passes at -O1 and -O2,
/// and at -O0 with a 64 MB stack.  Guaranteed tail calls through closure
/// values would need a different calling convention for crane::fn (a
/// trampoline, or [clang::musttail], which needs matching signatures
/// the thunk does not have): a design question, not this defect.  Kept in
/// wip until it is decided.
uint64_t CpsContinuationCopy::sumk(const List<uint64_t> &l,
                                   const crane::fn<uint64_t(uint64_t)> &k) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  crane::fn<uint64_t(uint64_t)> _loop_k = k;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return _loop_k(UINT64_C(0));
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      const List<uint64_t> &a1_value = *a1;
      _loop_k = [=](uint64_t s) { return _loop_k(a0 + s); };
      _loop_l = &a1_value;
    }
  }
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  while (true) {
    if (len <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t len0 = len - 1;
      auto _cell = typename List<uint64_t>::Cons(start, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      len = len0;
      start = (start + 1);
      continue;
    }
  }
  return std::move(*_root);
}
