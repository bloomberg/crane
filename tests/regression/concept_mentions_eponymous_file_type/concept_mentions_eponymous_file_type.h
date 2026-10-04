#ifndef INCLUDED_CONCEPT_MENTIONS_EPONYMOUS_FILE_TYPE
#define INCLUDED_CONCEPT_MENTIONS_EPONYMOUS_FILE_TYPE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
struct dshowNat;

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
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct List {
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a;
      std::shared_ptr<typename List::template list<A>> l;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    list(const typename List::template list<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<
                    typename List::template list<CraneU>::Nil>(_other.v())) {
              return Nil{};
            } else {
              const auto &[a, l] =
                  std::get<typename List::template list<CraneU>::Cons>(
                      _other.v());
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
                  (l ? std::make_shared<typename List::template list<A>>(
                           crane_convert<typename List::template list<A>>(*l))
                     : nullptr)};
            }
          }()) {}

    static typename List::template list<A> nil() {
      return typename List::template list<A>(Nil{});
    }

    static typename List::template list<A> cons(A a, List::list<A> l) {
      return typename List::template list<A>(Cons{
          std::move(a),
          std::make_shared<typename List::template list<A>>(std::move(l))});
    }

    // MANIPULATORS
    ~list() {
      auto _next = [&](variant_t &_v)
          -> std::shared_ptr<typename List::template list<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->l);
          }
        }
        return nullptr;
      };
      std::shared_ptr<typename List::template list<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    list(const list &) = default;
    list &operator=(const list &) = default;
    list(list &&) = default;
    list &operator=(list &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1>
  static std::optional<T1> nth_error(const List::list<T1> &l, const Nat &n);
};

template <typename a> using DList = crane::fn<List::list<a>(List::list<a>)>;
using DString = DList<bool>;
template <typename I, typename A>
concept DShow = requires {
  { I::dshow(std::declval<A>()) } -> std::convertible_to<DString>;
  { I::dlist(std::declval<A>()) } -> std::convertible_to<List::list<Nat>>;
};

struct dshowNat {
  static DString dshow(Nat) {
    return [](const List::list<bool> &l) {
      return List::template list<bool>::cons(true, l);
    };
  }

  static List::list<Nat> dlist(Nat n) {
    return List::template list<Nat>::cons(std::move(n),
                                          List::template list<Nat>::nil());
  }
};

static_assert(DShow<dshowNat, Nat>);

struct ConceptMentionsEponymousFileType {
  static inline const List::list<bool> run = dshowNat::dshow(
      Nat::s(Nat::s(Nat::s(Nat::o()))))(List::template list<bool>::nil());
  static inline const List::list<Nat> run2 =
      dshowNat::dlist(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))));
  static inline const std::optional<Nat> run3 = List::template nth_error<Nat>(
      dshowNat::dlist(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))),
      Nat::o());
};

template <typename T1>
std::optional<T1> List::nth_error(const List::list<T1> &l, const Nat &n) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    if (std::holds_alternative<typename List::list<T1>::Nil>(l.v())) {
      return std::optional<T1>();
    } else {
      const auto &[a00, a10] = std::get<typename List::list<T1>::Cons>(l.v());
      return std::make_optional<T1>(a00);
    }
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    if (std::holds_alternative<typename List::list<T1>::Nil>(l.v())) {
      return std::optional<T1>();
    } else {
      const auto &[a00, a10] = std::get<typename List::list<T1>::Cons>(l.v());
      return List::template nth_error<T1>(*a10, *a0);
    }
  }
}

#endif // INCLUDED_CONCEPT_MENTIONS_EPONYMOUS_FILE_TYPE
