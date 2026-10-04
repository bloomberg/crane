#include "loopify_computed_scrutinee_temp.h"

/// Loopification bug: a raw pointer into a *computed scrutinee temporary*
/// is stored in a stack frame that outlives the temporary.
///
/// walk is non-tail recursive and matches on wrap m l, a freshly
/// computed value rather than a variable. Loopification binds it as a
/// block-scoped temporary
///
/// auto &&_sv = wrap(m, l);
///
/// and then pushes the continuation frame
///
/// _stack.emplace_back(_Enter{crane_raw(a1), m});
///
/// where a1 is a field of _sv. The frame outlives the block, so the
/// next iteration reads *_f.l after _sv (and the cell it owned) has
/// been destroyed. hd l then observes recycled heap memory: the reads
/// happen after wrap's two make_shared calls have reused the block,
/// so the wrong answer shows up even without a sanitizer.
///
/// Rocq: go n = 7*n + n*(n-1)/2. Extracted C++ under-counts for n >= 2.
/// Removing Set Crane Loopify. makes the extracted code correct.
uint64_t
LoopifyComputedScrutineeTemp::hd(const LoopifyComputedScrutineeTemp::lst &l) {
  if (std::holds_alternative<typename LoopifyComputedScrutineeTemp::lst::Nil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename LoopifyComputedScrutineeTemp::lst::Cons>(l.v());
    return a0;
  }
}

LoopifyComputedScrutineeTemp::lst
LoopifyComputedScrutineeTemp::wrap(uint64_t m,
                                   const LoopifyComputedScrutineeTemp::lst &l) {
  return lst::cons(UINT64_C(7), lst::cons(m, l));
}

uint64_t LoopifyComputedScrutineeTemp::walk(
    uint64_t n, const LoopifyComputedScrutineeTemp::lst
                    &l) { /// CraneEnter: captures varying parameters for each
                          /// recursive call.

  struct CraneEnter {
    LoopifyComputedScrutineeTemp::lst l;
    uint64_t n;
  };

  /// CraneCont_Cons: saves [a0, l], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons {
    uint64_t a0;
    LoopifyComputedScrutineeTemp::lst l;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{l, n});
  /// Loopified walk: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyComputedScrutineeTemp::lst &l = std::move(_f.l);
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        auto &&_sv = wrap(m, l);
        if (std::holds_alternative<
                typename LoopifyComputedScrutineeTemp::lst::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] =
              std::get<typename LoopifyComputedScrutineeTemp::lst::Cons>(
                  _sv.v());
          _stack.emplace_back(CraneCont_Cons{a0, l});
          _stack.emplace_back(CraneEnter{*a1, m});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      const LoopifyComputedScrutineeTemp::lst &l = std::move(_f.l);
      _result = ((a0 + hd(l)) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyComputedScrutineeTemp::go(uint64_t n) {
  return walk(n, lst::nil());
}
