#ifndef INCLUDED_INSTANCE_IN_COLLISION_WRAPPER_NAMED_BARE
#define INCLUDED_INSTANCE_IN_COLLISION_WRAPPER_NAMED_BARE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
struct Ident;

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

  Nat add(Nat m) const {
    std::shared_ptr<Nat> _head{};
    std::shared_ptr<Nat> *_write = &_head;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        *_write = std::make_shared<Nat>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = std::make_shared<Nat>(typename Nat::S(nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename Nat::S>((*_write)->v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_head);
  }
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

template <typename I, typename A>
concept Dec = requires {
  { I::dec(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<bool>;
};

struct Ident {
  // TYPES
  struct Global {
    Nat n;
  };

  struct Local {
    Nat n;
  };

  using variant_t = std::variant<Global, Local>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Ident() {}

  explicit Ident(Global _v) : v_(std::move(_v)) {}

  explicit Ident(Local _v) : v_(std::move(_v)) {}

  static Ident global(Nat n) { return Ident(Global{std::move(n)}); }

  static Ident local(Nat n) { return Ident(Local{std::move(n)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct PeanoNat {
  static bool eqb(const Nat &n, const Nat &m);
};

struct Lookup {
  template <typename _tcI0, typename T1, typename T2>
    requires Dec<_tcI0, T1>
  static std::optional<T2> assoc(const T1 &k, const List<std::pair<T1, T2>> &l);
};

struct AstLike {
  struct Raw_id {
    // TYPES
    struct Name {
      Nat n;
    };

    struct Anon {
      Nat n;
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

    static Raw_id name(Nat n) { return Raw_id(Name{std::move(n)}); }

    static Raw_id anon(Nat n) { return Raw_id(Anon{std::move(n)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    Nat describe() const {
      if (std::holds_alternative<typename AstLike::Raw_id::Name>(this->v())) {
        const auto &[n0] = std::get<typename AstLike::Raw_id::Name>(this->v());
        if (AstLike::eq(n0, n0)) {
          return n0;
        } else {
          return Nat::o();
        }
      } else {
        const auto &[n0] = std::get<typename AstLike::Raw_id::Anon>(this->v());
        return n0;
      }
    }

    bool raw_id_eqb(const Raw_id &b) const {
      if (std::holds_alternative<typename AstLike::Raw_id::Name>(this->v())) {
        const auto &[n0] = std::get<typename AstLike::Raw_id::Name>(this->v());
        if (std::holds_alternative<typename AstLike::Raw_id::Name>(b.v())) {
          const auto &[n1] = std::get<typename AstLike::Raw_id::Name>(b.v());
          return PeanoNat::eqb(n0, n1);
        } else {
          return false;
        }
      } else {
        const auto &[n0] = std::get<typename AstLike::Raw_id::Anon>(this->v());
        if (std::holds_alternative<typename AstLike::Raw_id::Name>(b.v())) {
          return false;
        } else {
          const auto &[n1] = std::get<typename AstLike::Raw_id::Anon>(b.v());
          return PeanoNat::eqb(n0, n1);
        }
      }
    }
  };

  struct eq_dec_raw_id {
    static bool dec(AstLike::Raw_id a0, AstLike::Raw_id a1) {
      return a0.raw_id_eqb(std::move(a1));
    }
  };

  static_assert(Dec<eq_dec_raw_id, AstLike::Raw_id>);
  static Nat combine(const Nat &x0_, const Nat &x1_);
  static bool eq(const Nat &x0_, const Nat &x1_);
};

Ident to_ident(const AstLike::Raw_id &k);
std::pair<Nat, std::optional<Nat>>
find(const AstLike::Raw_id &k, const List<std::pair<AstLike::Raw_id, Nat>> &l);
std::pair<Ident, std::pair<Nat, std::optional<Nat>>>
both(const AstLike::Raw_id &k, const List<std::pair<AstLike::Raw_id, Nat>> &l);
std::pair<Nat, std::optional<Nat>>
both_at_one_site(const AstLike::Raw_id &k,
                 const List<std::pair<AstLike::Raw_id, Nat>> &l);

template <typename _tcI0, typename T1, typename T2>
  requires Dec<_tcI0, T1>
std::optional<T2> Lookup::assoc(const T1 &k, const List<std::pair<T1, T2>> &l) {
  if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(l.v())) {
    return std::optional<T2>();
  } else {
    const auto &[a0, a1] =
        std::get<typename List<std::pair<T1, T2>>::Cons>(l.v());
    const auto &[k_, v] = a0;
    if (_tcI0::dec(k, k_)) {
      return std::make_optional<T2>(v);
    } else {
      return Lookup::template assoc<_tcI0, T1, T2>(k, *a1);
    }
  }
}

#endif // INCLUDED_INSTANCE_IN_COLLISION_WRAPPER_NAMED_BARE
