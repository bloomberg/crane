#ifndef INCLUDED_LIST_CONS_ERASURE_BLEED
#define INCLUDED_LIST_CONS_ERASURE_BLEED

#include "crane_fn.h"
#include <algorithm>
#include <any>
#include <deque>
#include <type_traits>
#include <utility>
#include <variant>

template <typename T1> std::deque<std::any> _check_map(const std::deque<T1> l) {
  if (l.empty()) {
    return std::deque<std::any>{};
  } else {
    const auto &a = l.front();
    std::decay_t<decltype(l)> l0(l.begin() + 1, l.end());
    return [](auto _a0, auto _a1) {
      _a1.push_front(_a0);
      return _a1;
    }(std::any(), _check_map<T1>(l0));
  }
}

/// Regression test (now fixed). This mirrors theories/Parser/Defs.v's
/// concat_tuple/rev_tuple family verbatim (same tactic-built
/// dependent-case-split style, same
/// symbols_semty gamma := tuple (map symbol_semty gamma) domain), with
/// sym standing in for symbol. rev_tuple_cons_case calls
/// concat_tuple (rev xs') [x] (f xs' vs) (v, tt) -- where [x] : list sym
/// is a concrete singleton grammar-symbol list built in the SAME function
/// that also builds the erased singleton value tuple
/// (v, tt) : syms_semty [x]. check forces rev_tuple on a two-element
/// list so Crane must extract rev_tuple_cons_case for real.
///
/// Three bugs were fixed in src/translation.ml's gen_expr_custom_cons
/// (the custom-cons codegen for prod/list) and gen_custom_cpp_case:
///
/// 1. flows_into_erased_slot boxed a constructor argument into std::any
/// whenever the ENCLOSING function's return type resolved to std::any,
/// even when the argument being built was an unrelated CONCRETE value
/// (e.g. the singleton list [x] : list sym built inside a function
/// that separately returns an erased syms_semty). This produced
/// std::any(x) passed to the list's push_front, which only accepts
/// a concrete Sym -- "no matching member function for call to
/// 'push_front'". Fixed by excluding list-cons constructors from
/// flows_into_erased_slot (the boxing is only meaningful for
/// pair/tuple constructors).
///
/// 2. Even after (1), matching on rev_tuple's result in check crashed at
/// runtime with std::bad_any_cast. rev_tuple's Rocq-level type
/// (forall xs, syms_semty xs -> syms_semty (rev xs)) is a single
/// generic C++ function whose return type is the value-dependent-erased
/// syms_semty (std::any) -- but Rocq's type-checker concretely
/// reduces the call-site type ANNOTATION for a literal list argument
/// (e.g. [A; B]), making gen_custom_cpp_case believe the match
/// scrutinee was concretely typed and skip the any_cast<pair<any,any>>
/// needed to safely destructure it. Fixed by adding
/// scrut_callee_ret_erased, which looks up the callee's UN-INSTANTIATED
/// type scheme via find_type_opt (rather than relying solely on the
/// call-site-reduced annotation) to detect the erasure, together with a
/// flatten_app helper that strips curried MLapp nesting and
/// MLmagic-wrapped callee heads so the callee's MLglob head can be
/// recovered.
///
/// 3. Once (1) and (2) compiled cleanly, a further std::bad_any_cast
/// surfaced at runtime: the literal pair value (n, (n, tt)) passed as
/// an argument to rev_tuple (whose parameter type is the erased
/// syms_semty) was boxed as a single std::any holding the full
/// CONCRETE nested pair, instead of being erased component-by-component
/// to match what generic consumers (e.g. rev_tuple_cons_case's
/// any_cast<pair<any,any>>) expect at every nesting level -- and the
/// same issue affected pair literals built INSIDE a custom-cons's own
/// fields (e.g. (v, tt) in rev_tuple_cons_case, where v is itself
/// already read out of an erased slot via any_cast). Fixed by (a)
/// propagating the erased-return-slot context into nested prod-cons
/// fields instead of resetting it, so a nested pair also self-boxes its
/// own components, and (b) narrowing the "already erased, don't re-box"
/// guard in gen_expr_custom_cons from "any CPPany_cast" to
/// specifically "CPPany_cast (Tany, _)", since an any_cast to a
/// CONCRETE type (e.g. any_cast<uint64_t>(s)) still produces a raw,
/// un-boxed value that must be re-boxed to flow into a pair<any,any>
/// slot.
using tuple = std::any;
enum class Sym { A, B };
using sym_semty = uint64_t;
using syms_semty = tuple;
syms_semty concat_tuple_nil_case(const std::deque<Sym> &_x,
                                 const std::deque<Sym> &_x0, syms_semty _x1,
                                 syms_semty vs_);

template <typename F6>
  requires std::is_invocable_r_v<syms_semty, F6 &, std::deque<Sym> &,
                                 std::deque<Sym> &, syms_semty &, syms_semty &>
syms_semty concat_tuple_rec_case(Sym, const std::deque<Sym> &xs_,
                                 const std::deque<Sym> &,
                                 const std::deque<Sym> &ys, syms_semty vs,
                                 syms_semty vs_, F6 &&f) {
  const auto &[s, t] = std::any_cast<std::pair<std::any, std::any>>(vs);
  return std::make_pair(std::any(std::any_cast<sym_semty>(s)),
                        std::any(crane_call_erased(f, xs_, ys, t, vs_)));
}

syms_semty concat_tuple(const std::deque<Sym> &xs, const std::deque<Sym> &ys,
                        syms_semty vs, syms_semty vs_);
syms_semty rev_tuple_nil_case(const std::deque<Sym> &_x, syms_semty vs);

template <typename F4>
  requires std::is_invocable_r_v<syms_semty, F4 &, std::deque<Sym> &,
                                 syms_semty &>
syms_semty rev_tuple_cons_case(const std::deque<Sym> &, Sym x,
                               const std::deque<Sym> &xs_, syms_semty vs,
                               F4 &&f) {
  const auto &[s, t] = std::any_cast<std::pair<std::any, std::any>>(vs);
  return concat_tuple(
      [&]() {
        auto _r = xs_;
        std::reverse(_r.begin(), _r.end());
        return _r;
      }(),
      [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(x, std::deque<Sym>{}),
      crane_call_erased(f, xs_, t),
      std::make_pair(std::any(std::any_cast<sym_semty>(s)),
                     std::any(std::monostate{})));
}

syms_semty rev_tuple(const std::deque<Sym> &xs, syms_semty vs);
uint64_t check(uint64_t n);

#endif // INCLUDED_LIST_CONS_ERASURE_BLEED
