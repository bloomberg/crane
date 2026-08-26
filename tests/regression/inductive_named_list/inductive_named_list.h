#ifndef INCLUDED_INDUCTIVE_NAMED_LIST
#define INCLUDED_INDUCTIVE_NAMED_LIST

#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

struct InductiveNamedList {
  struct List_ {
    // TYPES
    struct LNil {};

    struct LCons {
      uint64_t a0;
      std::shared_ptr<List_> a1;
    };

    using variant_t = std::variant<LNil, LCons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    List_() {}

    explicit List_(LNil _v) : v_(_v) {}

    explicit List_(LCons _v) : v_(std::move(_v)) {}

    static List_ lnil() { return List_(LNil{}); }

    static List_ lcons(uint64_t a0, List_ a1) {
      return List_(LCons{a0, std::make_shared<List_>(std::move(a1))});
    }

    // MANIPULATORS
    ~List_() {
      crane::small_vector<std::shared_ptr<List_>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<LCons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
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

    List_(const List_ &) = default;
    List_ &operator=(const List_ &) = default;
    List_(List_ &&) noexcept = default;
    List_ &operator=(List_ &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, List_ &, T1 &>
  static T1 List_rect(T1 f, F1 &&f0, const List_ &l) {
    if (std::holds_alternative<typename List_::LNil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename List_::LCons>(l.v());
      return f0(a0, *a1, List_rect<T1>(f, f0, *a1));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, List_ &, T1 &>
  static T1 List_rec(T1 f, F1 &&f0, const List_ &l) {
    if (std::holds_alternative<typename List_::LNil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename List_::LCons>(l.v());
      return f0(a0, *a1, List_rec<T1>(f, f0, *a1));
    }
  }

  static uint64_t len(const List_ &l);
  static inline const uint64_t go =
      (len(List_::lcons(UINT64_C(1),
                        List_::lcons(UINT64_C(2), List_::lnil()))) +
       List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil()).length());
};

#endif // INCLUDED_INDUCTIVE_NAMED_LIST
