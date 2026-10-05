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
    const Nat &i) { /// CraneEnter: captures varying parameters for each
                    /// recursive call.

  struct CraneEnter {
    Nat i;
    LoopifyAdoptedFixNameShared::tree t;
  };

  using CraneFrame = std::variant<CraneEnter>;
  std::optional<Nat> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{i, t});
  /// Loopified f: CraneEnter.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    auto _f = std::move(std::get<CraneEnter>(_frame));
    const Nat &i = std::move(_f.i);
    const LoopifyAdoptedFixNameShared::tree &t = std::move(_f.t);
    crane::fn<std::optional<Nat>(std::optional<Nat>,
                                 List<LoopifyAdoptedFixNameShared::tree>, Nat)>
        struct_bytes = [](std::optional<Nat> pad,
                          const List<LoopifyAdoptedFixNameShared::tree> &x,
                          const Nat &x0) {
          auto loop = [&](const List<LoopifyAdoptedFixNameShared::tree> &ts,
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
          return loop(x, x0);
        };
    auto loop = [](const List<LoopifyAdoptedFixNameShared::tree> &ts,
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
