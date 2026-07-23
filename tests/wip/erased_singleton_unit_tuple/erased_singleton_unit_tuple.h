#ifndef INCLUDED_ERASED_SINGLETON_UNIT_TUPLE
#define INCLUDED_ERASED_SINGLETON_UNIT_TUPLE

#include <any>
#include <memory>
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

/// Runtime bad_any_cast repro. After all the compile-time leaf-forward bugs
/// were fixed, the extracted parsers COMPILE but crash at runtime with
/// std::bad_any_cast during parse_*. Root cause is Crane's codegen for
/// theories/Parser/Defs.v's rev_tuple_cons_case:
/// exact (concat_tuple (rev xs') x (f xs' vs) (v, tt)).
/// The singleton tuple (v, tt) : symbols_semty [x] -- where symbols_semty
/// gamma := tuple (map symbol_semty gamma) erases to std::any and v is
/// destructured from an erased tuple (so it is std::any) -- is emitted by Crane
/// (Defs.h:340) as
/// std::make_pair(s, std::monostate{})
/// i.e. a std::pair<std::any, std::monostate>: the tt : unit component is
/// left as a raw std::monostate{} instead of being erased to
/// std::any(std::monostate{}). So the value's dynamic type is
/// pair<any, monostate>. But every consumer of an erased symbols_semty
/// destructures with std::any_cast<std::pair<std::any, std::any>>(...), which
/// requires the boxed type to be EXACTLY pair<any,any> -> std::bad_any_cast at
/// runtime (the LL parser hits this in Parser.h applying a production's
/// predicate/action to the reversed RHS-values tuple vs_ = rev_tuple ...).
///
/// Repro: cons_sem builds erased tuples correctly (generic over head symbol
/// and tail list -> Crane emits make_pair(any(v), rest), a proper
/// pair<any,any>). head1 mirrors rev_tuple_cons_case's (v, tt): a singleton
/// erased tuple from an erased head -> Crane emits the buggy make_pair(any_v,
/// monostate{}). firstOf is a generic consumer destructuring an erased tuple as
/// pair<any,any>. check feeds head1's output into firstOf and throws
/// std::bad_any_cast at runtime, because head1 produced pair<any,monostate> but
/// firstOf any_casts to pair<any,any>. (cons_sem is used to build the input so
/// we avoid an unrelated concrete-literal-to-erased coercion artifact at
/// static-init time.)
using tuple = std::any;
enum class Sym { A, B };
using sym_semty = std::any;
using syms_semty = tuple;
syms_semty cons_sem(Sym _x, const List<Sym> &_x0, sym_semty v, syms_semty rest);
syms_semty head1(const List<Sym> &_x, syms_semty vs);
uint64_t firstOf(const List<Sym> &_x, syms_semty t);
uint64_t check(uint64_t n);

#endif // INCLUDED_ERASED_SINGLETON_UNIT_TUPLE
