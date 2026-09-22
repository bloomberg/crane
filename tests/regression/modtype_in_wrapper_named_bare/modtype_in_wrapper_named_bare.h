#ifndef INCLUDED_MODTYPE_IN_WRAPPER_NAMED_BARE
#define INCLUDED_MODTYPE_IN_WRAPPER_NAMED_BARE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
struct Collider;
struct Raw_id;
template <typename M>
concept Ord = requires {
  typename M::t;
  {
    M::eq_dec(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<bool>;
};

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ =
          Cons{[&]() -> A {
                 if constexpr (crane_convertible<A, const _U &>) {
                   return crane_convert<A>(a);
                 } else {
                   throw std::logic_error("unreachable: inactive constructor "
                                          "field at this instantiation");
                 }
               }(),
               (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                  : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
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
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Collider {
  // TYPES
  struct Tag0 {};

  struct Tag1 {
    Nat a0;
  };

  using variant_t = std::variant<Tag0, Tag1>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Collider() {}

  explicit Collider(Tag0 _v) : v_(_v) {}

  explicit Collider(Tag1 _v) : v_(std::move(_v)) {}

  static Collider tag0() { return Collider(Tag0{}); }

  static Collider tag1(Nat a0) { return Collider(Tag1{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct PeanoNat {
  static bool leb(const Nat &n, const Nat &m);
  static bool eq_dec(const Nat &n, const Nat &m);
};

struct Raw_id {
  // TYPES
  struct Name {
    Nat a0;
  };

  struct Anon {
    Nat a0;
  };

  using variant_t = std::variant<Name, Anon>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Raw_id() {}

  explicit Raw_id(Name _v) : v_(std::move(_v)) {}

  explicit Raw_id(Anon _v) : v_(std::move(_v)) {}

  static Raw_id name(Nat a0) { return Raw_id(Name{std::move(a0)}); }

  static Raw_id anon(Nat a0) { return Raw_id(Anon{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool raw_id_dec(const Raw_id &y) const;
};

struct AstLib {
  struct RawIDOrd {
    using t = Raw_id;
    static bool eq_dec(t x0_, t x1_);
  };

  static Nat pick(Nat a, Nat b);
};

template <Ord X> struct Make {
  template <typename elt> using tbl = List<std::pair<typename X::t, elt>>;

  template <typename T1> static const tbl<T1> &empty() {
    static const tbl<T1> v = List<std::pair<typename X::t, T1>>::nil();
    return v;
  }
};

bool viaQualified(const Raw_id &a, const Raw_id &b);
using RM = Make<AstLib::RawIDOrd>;
const RM::template tbl<bool> start = RM::template empty<bool>();
Nat viaColliding(const Nat &x0_, const Nat &x1_);
Nat keepColl(const Collider &r);

inline bool Raw_id::raw_id_dec(const Raw_id &y) const {
  if (std::holds_alternative<typename Raw_id::Name>(this->v())) {
    const auto &[a0] = std::get<typename Raw_id::Name>(this->v());
    if (std::holds_alternative<typename Raw_id::Name>(y.v())) {
      const auto &[a00] = std::get<typename Raw_id::Name>(y.v());
      if (PeanoNat::eq_dec(a0, a00)) {
        return true;
      } else {
        return false;
      }
    } else {
      return false;
    }
  } else {
    const auto &[a0] = std::get<typename Raw_id::Anon>(this->v());
    if (std::holds_alternative<typename Raw_id::Name>(y.v())) {
      return false;
    } else {
      const auto &[a00] = std::get<typename Raw_id::Anon>(y.v());
      if (PeanoNat::eq_dec(a0, a00)) {
        return true;
      } else {
        return false;
      }
    }
  }
}

#endif // INCLUDED_MODTYPE_IN_WRAPPER_NAMED_BARE
