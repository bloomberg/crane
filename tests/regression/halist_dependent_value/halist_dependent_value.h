#ifndef INCLUDED_HALIST_DEPENDENT_VALUE
#define INCLUDED_HALIST_DEPENDENT_VALUE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename A> struct Sig;
template <typename A, typename P> struct SigT;

struct Sumbool {
  static Sig<bool> bool_of_sumbool(bool s);
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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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

  template <typename F0> List<A> filter(F0 &&f) const {
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<A>::nil();
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        if (f(a0)) {
          auto _cell = typename List<A>::Cons(a0, nullptr);
          List<A> &_node =
              (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
          _loop_self = crane_raw(a1);
          continue;
        } else {
          _loop_self = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  template <typename CraneU>
    requires crane_convertible<CraneU, const A &>
  operator Sig<CraneU>() const {
    return {crane_convert<CraneU>(x)};
  }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename CraneU0, typename CraneU1>
    requires crane_convertible<CraneU0, const A &> &&
             crane_convertible<CraneU1, const P &>
  operator SigT<CraneU0, CraneU1>() const {
    return {crane_convert<CraneU0>(x), crane_convert<CraneU1>(a1)};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }

  A projT1() const {
    const auto &[x0, a1] = *this;
    return x0;
  }
};

template <typename a> using EqDec = crane::fn<bool(a, a)>;

struct EquivDec {
  template <typename T1>
  static bool equiv_dec(std::type_identity_t<EqDec<T1>> eqDec, const T1 &x0_,
                        T1 x1_);
};

template <typename k, typename v> using halist = List<SigT<k, v>>;

struct HAList0 {
  template <typename T1, typename T2>
  static halist<T1, T2> halist_remove(std::type_identity_t<EqDec<T1>> eq,
                                      const T1 &k, const List<SigT<T1, T2>> &m);
  template <typename T1, typename T2>
  static halist<T1, T2> halist_add(std::type_identity_t<EqDec<T1>> eq,
                                   const T1 &k, const T2 &v,
                                   const List<SigT<T1, T2>> &m);
  template <typename T1, typename T2>
  static std::optional<T2> halist_lookup(std::type_identity_t<EqDec<T1>> eq,
                                         const T1 &k,
                                         const List<SigT<T1, T2>> &l);
};

/// halist K V is indexed by a value family V : K -> Type.  Crane gives
/// halist_add the signature halist<T1,T2> halist_add(EqDec<T1>, T1 k, T2 v,
/// ...) -- the same template parameter T2 stands for the family and for the
/// value.  T2 is deduced as vty from the map argument, so passing a
/// uint64_t for v leaves no viable overload.
struct HalistDependentValue {
  enum class Key { KNAT, KLIST };

  template <typename T1> static T1 key_rect(T1 f, T1 f0, Key k) {
    switch (k) {
    case Key::KNAT: {
      return f;
    }
    case Key::KLIST: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 key_rec(const T1 &f, const T1 &f0, Key k) {
    return key_rect<T1>(f, f0, k);
  }

  using vty = crane::obj;
  static inline const EqDec<Key> keyEq = [](Key x, Key y) -> bool {
    switch (x) {
    case Key::KNAT: {
      switch (y) {
      case Key::KNAT: {
        return true;
      }
      case Key::KLIST: {
        return false;
      }
      default:
        std::unreachable();
      }
      break;
    }
    case Key::KLIST: {
      switch (y) {
      case Key::KNAT: {
        return false;
      }
      case Key::KLIST: {
        return true;
      }
      default:
        std::unreachable();
      }
      break;
    }
    default:
      std::unreachable();
    }
  };
  static inline const halist<Key, vty> m0 = List<SigT<Key, crane::obj>>::nil();
  static inline const halist<Key, vty> m1 =
      HAList0::halist_add(keyEq, Key::KNAT, crane::obj(UINT64_C(7)), m0);
  static inline const halist<Key, vty> m2 = HAList0::halist_add(
      keyEq, Key::KLIST,
      crane::obj(List<crane::obj>::cons(
          UINT64_C(1),
          List<crane::obj>::cons(
              UINT64_C(2),
              List<crane::obj>::cons(UINT64_C(3), List<crane::obj>::nil())))),
      m1);
  static inline const uint64_t run = ([]() -> uint64_t {
    auto _cs = HAList0::halist_lookup(keyEq, Key::KNAT, m2);
    if (_cs.has_value()) {
      const auto &n = *_cs;
      return crane::any_cast<uint64_t>(n);
    } else {
      return UINT64_C(0);
    }
  }() + []() -> uint64_t {
    auto _cs1 = HAList0::halist_lookup(keyEq, Key::KLIST, m2);
    if (_cs1.has_value()) {
      const auto &l = *_cs1;
      return List<uint64_t>(crane::any_cast<List<crane::obj>>(l)).length();
    } else {
      return UINT64_C(0);
    }
  }());
};

template <typename T1>
bool EquivDec::equiv_dec(std::type_identity_t<EqDec<T1>> eqDec, const T1 &x0_,
                         T1 x1_) {
  return eqDec(x0_, std::move(x1_));
}

template <typename T1, typename T2>
halist<T1, T2> HAList0::halist_remove(std::type_identity_t<EqDec<T1>> eq,
                                      const T1 &k,
                                      const List<SigT<T1, T2>> &m) {
  return m.filter([=](const SigT<T1, T2> &k_v) {
    return !([&]() {
      const auto &_sv =
          Sumbool::bool_of_sumbool(EquivDec::equiv_dec(eq, k_v.projT1(), k));
      const auto &[x] = _sv;
      return x;
    }());
  });
}

template <typename T1, typename T2>
halist<T1, T2> HAList0::halist_add(std::type_identity_t<EqDec<T1>> eq,
                                   const T1 &k, const T2 &v,
                                   const List<SigT<T1, T2>> &m) {
  return List<SigT<T1, T2>>::cons(
      SigT<T1, T2>::existt(k, v),
      HAList0::template halist_remove<T1, T2>(std::move(eq), k, m));
}

template <typename T1, typename T2>
std::optional<T2> HAList0::halist_lookup(std::type_identity_t<EqDec<T1>> eq,
                                         const T1 &k,
                                         const List<SigT<T1, T2>> &l) {
  if (std::holds_alternative<typename List<SigT<T1, T2>>::Nil>(l.v())) {
    return std::optional<T2>();
  } else {
    const auto &[a0, a1] = std::get<typename List<SigT<T1, T2>>::Cons>(l.v());
    const auto &[x0, a10] = a0;
    if (EquivDec::equiv_dec(eq, x0, k)) {
      return std::make_optional<T2>(a10);
    } else {
      return HAList0::template halist_lookup<T1, T2>(eq, k, *a1);
    }
  }
}

#endif // INCLUDED_HALIST_DEPENDENT_VALUE
