#ifndef INCLUDED_CONCEPT_MENTIONS_EPONYMOUS_FILE_TYPE
#define INCLUDED_CONCEPT_MENTIONS_EPONYMOUS_FILE_TYPE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
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

    template <typename _U>
    list(const typename List::template list<_U> &_other) {
      if (std::holds_alternative<typename List::template list<_U>::Nil>(
              _other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a, l] =
            std::get<typename List::template list<_U>::Cons>(_other.v());
        this->v_ =
            Cons{[&]() -> A {
                   if constexpr (crane_convertible<A, const _U &>) {
                     return crane_convert<A>(a);
                   } else {
                     throw std::logic_error("unreachable: inactive constructor "
                                            "field at this instantiation");
                   }
                 }(),
                 (l ? std::make_shared<typename List::template list<A>>(
                          crane_convert<typename List::template list<A>>(*l))
                    : nullptr)};
      }
    }

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
      crane::small_vector<std::shared_ptr<typename List::template list<A>>>
          _stack = {};
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

    list(const list &) = default;
    list &operator=(const list &) = default;
    list(list &&) noexcept = default;
    list &operator=(list &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1>
  static std::optional<T1> nth_error(const List::list<T1> &l, const Nat &n);
};

template <typename a> using DList = std::function<List::list<a>(List::list<a>)>;
using DString = DList<bool>;
template <typename I, typename A>
concept DShow = requires {
  { I::dshow(std::declval<A>()) } -> std::convertible_to<DString>;
  { I::dlist(std::declval<A>()) } -> std::convertible_to<List::list<Nat>>;
};

struct dshowNat {
  static DString dshow(Nat) {
    return [](List::list<bool> l) {
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
