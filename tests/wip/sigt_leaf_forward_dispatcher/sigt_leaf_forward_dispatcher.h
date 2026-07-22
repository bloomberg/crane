#ifndef INCLUDED_SIGT_LEAF_FORWARD_DISPATCHER
#define INCLUDED_SIGT_LEAF_FORWARD_DISPATCHER

#include <any>
#include <functional>
#include <memory>
#include <string>
#include <utility>
#include <variant>
#include <vector>

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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

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

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

struct Bool {
  static bool eqb(bool b1, bool b2);
};

struct Ascii {
  static bool eqb0(char a, char b);
};

struct String {
  static bool eqb1(const std::string &s1, const std::string &s2);
};

/// All prior attempts wrote the action closure directly at the entry's
/// definition site (my_entry := existT psem (0,[]) ((fun tup => ...), ...)),
/// which Crane always concretizes (the generated lambda's parameter is a
/// concrete pair type, not auto). The REAL grammar table
/// (Parser.v/Defs.v) instead builds every production's predicate/action
/// through a SINGLE shared dispatcher function with one big match over
/// the production id -- e.g. production_action (p : production) :
/// predicate_semty p * action_semty p := match p with ... end -- and only
/// THEN stores existT psem p (production_action p) per entry. This test
/// checks whether routing the action through such a shared dispatcher (one
/// function, many match arms, each returning a differently-typed closure)
/// is what forces Crane to emit a genuinely generic auto-parameterized
/// lambda (hitting crane_erase_fn's buggy generic branch) instead of a
/// concretely-typed one -- which would explain why Newick.h/PPM.h/XML.h
/// still fail after all prior fixes.
bool wrap_string(const std::string &s);
using domty = std::any;
using prod2 = std::pair<uint64_t, List<uint64_t>>;
using pred_ty = std::any;
using act_ty = std::any;
using psem = std::pair<pred_ty, act_ty>;
using entry = SigT<prod2, psem>;
bool mk_action(uint64_t n, std::any tup);
const entry my_entry = SigT<prod2, psem>::existt(
    std::make_pair(UINT64_C(0), List<uint64_t>::nil()),
    std::make_pair(
        [](domty _x0) -> bool { return mk_action(UINT64_C(0), _x0); },
        [](domty _x0) -> bool { return mk_action(UINT64_C(0), _x0); }));
domty garg(uint64_t n);
bool run(const SigT<std::pair<uint64_t, List<uint64_t>>,
                    std::pair<std::any, std::any>> &e);
bool check(std::monostate _x);

#endif // INCLUDED_SIGT_LEAF_FORWARD_DISPATCHER
