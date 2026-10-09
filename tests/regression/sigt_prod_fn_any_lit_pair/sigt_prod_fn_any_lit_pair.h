#ifndef INCLUDED_SIGT_PROD_FN_ANY_LIT_PAIR
#define INCLUDED_SIGT_PROD_FN_ANY_LIT_PAIR

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "shared_block.h"
#include <atomic>
#include <functional>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename A, typename P> struct SigT;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename CraneU0, typename CraneU1>
  operator SigT<CraneU0, CraneU1>() const {
    return {[&]() -> CraneU0 {
              if constexpr (crane_convertible<CraneU0, const A &>) {
                return crane_convert<CraneU0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const P &>) {
                return crane_convert<CraneU1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

template <typename M>
concept SEM = requires {
  typename M::idx;
  typename M::sem;
};

/// Same shape as sigt_prod_fn_any_lit (grammar entry = sigma-type pairing a
/// production with an erased predicate/action pair), but here the
/// predicate/action *domain* is itself a concrete pair `sem a * unit`
/// (mirroring symbols_semty ys := symbol_semty y * symbols_semty ys' in
/// theories/Parser/Defs.v), so the inline generic lambda body structurally
/// destructures its argument via `let (v, _x) := tup`.
///
/// This used to fail to *compile*: the lambda is stored via crane_erase_fn
/// (its domain is partly erased), so at runtime it is only ever invoked with
/// its whole argument boxed as a single raw std::any — but the generated
/// parameter was a generic auto& that, once deduced as std::any, can't be
/// destructured via a structured binding (std::any is not tuple-like).
/// Fixed by mark_own_param_for_pair_erasure (translation.ml): when a
/// lambda literal is about to be routed through crane_erase_fn, its
/// immediate self-match on its own parameter is marked MLmagic so the
/// scrutinee is any_cast to pair<any,any> before destructuring, matching
/// what run's application site actually constructs and passes.
template <SEM S> struct Make {
  using dom = std::pair<crane::obj, std::monostate>;
  using prod2 = std::pair<typename S::idx, List<typename S::idx>>;
  using pred_ty = crane::obj;
  using act_ty = crane::obj;
  using psem = std::pair<pred_ty, act_ty>;
  using entry = SigT<prod2, psem>;

  static entry mk_entry(typename S::idx a) {
    static const auto erased_fn =
        crane::immortal(crane_erase_fn([](const auto &tup) {
          const auto &[_x, _x0] =
              crane::any_cast<std::pair<crane::obj, crane::obj>>(tup);
          return true;
        }));
    return SigT<prod2, psem>::existt(
        std::make_pair(std::move(a), List<typename S::idx>::nil()),
        std::make_pair(crane::obj(erased_fn), crane::obj(erased_fn)));
  }

  template <typename F1>
  static bool run(const SigT<std::pair<typename S::idx, List<typename S::idx>>,
                             std::pair<crane::obj, crane::obj>> &e,
                  F1 &&arg) {
    const auto &[x0, a1] = e;
    const auto &[a, _x] = x0;
    const auto &[f, _x0] = a1;
    if (crane::any_cast<bool>(
            crane::any_cast<crane::fn<crane::obj(crane::obj)>>(f)(
                std::make_pair(crane::obj(arg(a)),
                               crane::obj(std::monostate{}))))) {
      return true;
    } else {
      return false;
    }
  }
};

struct Inst {
  using idx = std::monostate;
  using sem = bool;
};

using M = Make<Inst>;
const M::entry my_entry = M::mk_entry(std::monostate{});
Inst::sem my_arg(std::monostate _x);
bool check(std::monostate _x);

#endif // INCLUDED_SIGT_PROD_FN_ANY_LIT_PAIR
