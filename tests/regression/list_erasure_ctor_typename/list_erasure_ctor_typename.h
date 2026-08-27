#ifndef INCLUDED_LIST_ERASURE_CTOR_TYPENAME
#define INCLUDED_LIST_ERASURE_CTOR_TYPENAME

#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

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
                  return A{
                      [&]() -> typename A::first_type {
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
            l ? std::make_shared<typename List::template list<A>>(*l)
              : nullptr};
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
  static std::optional<T1> nth_error(const List::list<T1> &l, uint64_t n);
};

/// Using nth_error on a list (nat -> nat) instantiates the
/// erasure-converting List constructor, whose body names the source
/// instantiation's constructor structs.  Because list is not merged into
/// its List wrapper struct, those names are dependent and must be spelled
/// typename List::template list<_U>::Nil.
struct ListErasureCtorTypename {
  static std::optional<std::function<uint64_t(uint64_t)>> pick(uint64_t n);
  static inline const uint64_t go = []() -> uint64_t {
    auto _cs = pick(UINT64_C(1));
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(21));
    } else {
      return UINT64_C(0);
    }
  }();
};

template <typename T1>
std::optional<T1> List::nth_error(const List::list<T1> &l, uint64_t n) {
  if (n <= 0) {
    if (std::holds_alternative<typename List::list<T1>::Nil>(l.v())) {
      return std::optional<T1>();
    } else {
      const auto &[a0, a1] = std::get<typename List::list<T1>::Cons>(l.v());
      return std::make_optional<T1>(a0);
    }
  } else {
    uint64_t n0 = n - 1;
    if (std::holds_alternative<typename List::list<T1>::Nil>(l.v())) {
      return std::optional<T1>();
    } else {
      const auto &[a00, a10] = std::get<typename List::list<T1>::Cons>(l.v());
      return List::template nth_error<T1>(*a10, n0);
    }
  }
}

#endif // INCLUDED_LIST_ERASURE_CTOR_TYPENAME
