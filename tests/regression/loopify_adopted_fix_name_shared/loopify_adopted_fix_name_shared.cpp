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
  crane::fn<std::optional<Nat>(std::optional<Nat>,
                               List<LoopifyAdoptedFixNameShared::tree>, Nat)>
      struct_bytes = [](std::optional<Nat> pad,
                        const List<LoopifyAdoptedFixNameShared::tree> &x,
                        const Nat &x0) {
        auto loop = [&](const List<LoopifyAdoptedFixNameShared::tree> &ts,
                        Nat k) -> std::optional<Nat> {
          Nat _loop_k = std::move(k);
          const List<LoopifyAdoptedFixNameShared::tree> *_loop_ts = &ts;
          while (true) {
            if (std::holds_alternative<
                    typename List<LoopifyAdoptedFixNameShared::tree>::Nil>(
                    _loop_ts->v())) {
              if (pad.has_value()) {
                const Nat &p = *pad;
                return std::make_optional<Nat>(p.add(std::move(_loop_k)));
              } else {
                return std::optional<Nat>();
              }
            } else {
              const auto &[a0, a1] = std::get<
                  typename List<LoopifyAdoptedFixNameShared::tree>::Cons>(
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
  auto loop = [](const List<LoopifyAdoptedFixNameShared::tree> &ts,
                 Nat k) -> std::optional<Nat> {
    Nat _loop_k = std::move(k);
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
          return f(a0, std::move(_loop_k));
        } else {
          _loop_k = _loop_k.sub(Nat::s(Nat::s(Nat::o())));
          _loop_ts = crane_raw(a1);
        }
      }
    }
  };
  if (std::holds_alternative<typename LoopifyAdoptedFixNameShared::tree::Leaf>(
          t.v())) {
    const auto &[n0] =
        std::get<typename LoopifyAdoptedFixNameShared::tree::Leaf>(t.v());
    return std::make_optional<Nat>(n0.add(std::move(i)));
  } else if (std::holds_alternative<
                 typename LoopifyAdoptedFixNameShared::tree::Node>(t.v())) {
    const auto &[ts0] =
        std::get<typename LoopifyAdoptedFixNameShared::tree::Node>(t.v());
    return struct_bytes(std::make_optional<Nat>(Nat::s(Nat::o())), *ts0,
                        std::move(i));
  } else {
    const auto &[ts0] =
        std::get<typename LoopifyAdoptedFixNameShared::tree::Arr>(t.v());
    return loop(*ts0, std::move(i));
  }
}
