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
std::optional<Nat> LoopifyAdoptedFixNameShared::f(
    const LoopifyAdoptedFixNameShared::tree &t,
    const Nat
        &i) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    Nat i;
    LoopifyAdoptedFixNameShared::tree t;
  };

  using _Frame = std::variant<_Enter>;
  std::optional<Nat> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{i, t});
  /// Loopified f: _Enter.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    auto _f = std::move(std::get<_Enter>(_frame));
    const Nat &i = std::move(_f.i);
    const LoopifyAdoptedFixNameShared::tree &t = std::move(_f.t);
    crane::fn<std::optional<Nat>(std::optional<Nat>,
                                 List<LoopifyAdoptedFixNameShared::tree>, Nat)>
        struct_bytes = [=](std::optional<Nat> pad,
                           const List<LoopifyAdoptedFixNameShared::tree> &x,
                           const Nat &x0) {
          auto loop_impl =
              [&](auto &, const List<LoopifyAdoptedFixNameShared::tree> &ts,
                  const Nat &k) -> std::optional<Nat> {
            Nat _loop_k = k;
            const List<LoopifyAdoptedFixNameShared::tree> *_loop_ts = &ts;
            while (true) {
              if (std::holds_alternative<
                      typename List<LoopifyAdoptedFixNameShared::tree>::Nil>(
                      _loop_ts->v())) {
                if (pad.has_value()) {
                  const Nat &p = *pad;
                  return std::make_optional<Nat>(p.add(_loop_k));
                } else {
                  return std::optional<Nat>();
                }
              } else {
                const auto &[a0, a1] = std::get<
                    typename List<LoopifyAdoptedFixNameShared::tree>::Cons>(
                    _loop_ts->v());
                if (_loop_k.ltb(Nat::s(Nat::s(Nat::s(Nat::o()))))) {
                  return f(a0, _loop_k);
                } else {
                  _loop_k = _loop_k.sub(Nat::s(Nat::s(Nat::s(Nat::o()))));
                  _loop_ts = crane_raw(a1);
                }
              }
            }
          };
          auto loop = [&](const List<LoopifyAdoptedFixNameShared::tree> &ts,
                          const Nat &k) -> std::optional<Nat> {
            return loop_impl(loop_impl, ts, k);
          };
          return loop(x, x0);
        };
    auto loop_impl = [&](auto &,
                         const List<LoopifyAdoptedFixNameShared::tree> &ts,
                         const Nat &k) -> std::optional<Nat> {
      Nat _loop_k = k;
      const List<LoopifyAdoptedFixNameShared::tree> *_loop_ts = &ts;
      while (true) {
        if (std::holds_alternative<
                typename List<LoopifyAdoptedFixNameShared::tree>::Nil>(
                _loop_ts->v())) {
          return std::optional<Nat>();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<LoopifyAdoptedFixNameShared::tree>::Cons>(
                  _loop_ts->v());
          if (_loop_k.ltb(Nat::s(Nat::s(Nat::o())))) {
            return f(a0, _loop_k);
          } else {
            _loop_k = _loop_k.sub(Nat::s(Nat::s(Nat::o())));
            _loop_ts = crane_raw(a1);
          }
        }
      }
    };
    auto loop = [&](const List<LoopifyAdoptedFixNameShared::tree> &ts,
                    const Nat &k) -> std::optional<Nat> {
      return loop_impl(loop_impl, ts, k);
    };
    if (std::holds_alternative<
            typename LoopifyAdoptedFixNameShared::tree::Leaf>(t.v())) {
      const auto &[n0] =
          std::get<typename LoopifyAdoptedFixNameShared::tree::Leaf>(t.v());
      _result = std::make_optional<Nat>(n0.add(i));
    } else if (std::holds_alternative<
                   typename LoopifyAdoptedFixNameShared::tree::Node>(t.v())) {
      const auto &[ts0] =
          std::get<typename LoopifyAdoptedFixNameShared::tree::Node>(t.v());
      _result =
          struct_bytes(std::make_optional<Nat>(Nat::s(Nat::o())), *ts0, i);
    } else {
      const auto &[ts0] =
          std::get<typename LoopifyAdoptedFixNameShared::tree::Arr>(t.v());
      _result = loop(*ts0, i);
    }
  }
  return _result;
}
