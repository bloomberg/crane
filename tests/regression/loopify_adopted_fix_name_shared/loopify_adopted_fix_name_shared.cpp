#include "loopify_adopted_fix_name_shared.h"

/// Crane bug (compile error): under Set Crane Loopify, a function whose
/// body let-binds two local fixpoints of the same name -- both loop, the
/// first inside a lambda -- adopts one as a second machine entry, and
/// installing the adoption reroutes calls by name.  The names are shared
/// (loop_impl, loop, _self_loop), so the other fixpoint's calls were
/// rerouted too, to an entry that never handles them:
/// error: use of undeclared identifier '_adopted_loop'
///
/// Reduced from Vellvm, Semantics/MemoryBytes.v:112
/// (dvalue_extract_byte: dvalue_extract_struct_bytes under its pad
/// lambda, and dvalue_extract_array_bytes).
std::optional<Nat>
LoopifyAdoptedFixNameShared::f(const LoopifyAdoptedFixNameShared::tree &t,
                               Nat i) {
  // Explicit stack replaces the non-tail recursion of f: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    Nat i;
    const LoopifyAdoptedFixNameShared::tree *t;
  };

  struct _call_loop {
    Nat k;
    const List<LoopifyAdoptedFixNameShared::tree> *ts;
  };

  using _frame = std::variant<_call, _call_loop>;
  std::optional<Nat> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{std::move(i), &t});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      Nat i = std::move(_f.i);
      const LoopifyAdoptedFixNameShared::tree &t = *_f.t;
      crane::fn<
          std::optional<Nat>(std::optional<Nat>,
                             List<LoopifyAdoptedFixNameShared::tree>,
                             Nat)> struct_bytes =
          [](std::optional<Nat> pad,
             const List<LoopifyAdoptedFixNameShared::tree> &x, const Nat &x0) {
            auto loop =
                [&](const List<LoopifyAdoptedFixNameShared::tree> &ts,
                    Nat k)
                     -> std::optional<Nat> {
                  // Loop replaces the tail recursion: each recursive call
                  // updates the loop variables.
                  Nat _loop_k = std::move(k);
                  const List<LoopifyAdoptedFixNameShared::tree> *_loop_ts = &ts;
                  while (true) {
                    if (std::holds_alternative<typename List<
                            LoopifyAdoptedFixNameShared::tree>::Nil>(
                            _loop_ts->v())) {
                      if (pad.has_value()) {
                        const Nat &p = *pad;
                        return std::make_optional<Nat>(
                            p.add(std::move(_loop_k)));
                      } else {
                        return std::optional<Nat>();
                      }
                    } else {
                      const auto &[a0, a1] = std::get<typename List<
                          LoopifyAdoptedFixNameShared::tree>::Cons>(
                          _loop_ts->v());
                      if (_loop_k.ltb(Nat::s(Nat::s(Nat::s(Nat::o()))))) {
                        return f(a0, std::move(_loop_k));
                      } else {
                        _loop_k = _loop_k.sub(Nat::s(Nat::s(Nat::s(Nat::o()))));
                        _loop_ts = crane_raw(a1);
                      }
                    }
                  }
                };
            return loop(x, x0);
          };
      if (std::holds_alternative<
              typename LoopifyAdoptedFixNameShared::tree::Leaf>(t.v())) {
        const auto &[n0] =
            std::get<typename LoopifyAdoptedFixNameShared::tree::Leaf>(t.v());
        _result = std::make_optional<Nat>(n0.add(std::move(i)));
      } else if (std::holds_alternative<
                     typename LoopifyAdoptedFixNameShared::tree::Node>(t.v())) {
        const auto &[ts0] =
            std::get<typename LoopifyAdoptedFixNameShared::tree::Node>(t.v());
        _result = struct_bytes(std::make_optional<Nat>(Nat::s(Nat::o())), *ts0,
                               std::move(i));
      } else {
        const auto &[ts0] =
            std::get<typename LoopifyAdoptedFixNameShared::tree::Arr>(t.v());
        _stack.emplace_back(_call_loop{std::move(i), crane_raw(ts0)});
      }
    } else {
      auto _f = std::move(std::get<_call_loop>(_popped));
      Nat k = std::move(_f.k);
      const List<LoopifyAdoptedFixNameShared::tree> &ts = *_f.ts;
      if (std::holds_alternative<
              typename List<LoopifyAdoptedFixNameShared::tree>::Nil>(ts.v())) {
        _result = std::optional<Nat>();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyAdoptedFixNameShared::tree>::Cons>(
                ts.v());
        if (k.ltb(Nat::s(Nat::s(Nat::o())))) {
          _stack.emplace_back(_call{std::move(k), &a0});
        } else {
          _stack.emplace_back(
              _call_loop{k.sub(Nat::s(Nat::s(Nat::o()))), crane_raw(a1)});
        }
      }
    }
  }
  return _result;
}
