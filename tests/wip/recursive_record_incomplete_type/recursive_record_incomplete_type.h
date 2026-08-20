#ifndef INCLUDED_RECURSIVE_RECORD_INCOMPLETE_TYPE
#define INCLUDED_RECURSIVE_RECORD_INCOMPLETE_TYPE

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
};

struct RecursiveRecordIncompleteType {
  /// A record-shaped inductive whose recursion runs through a list. Written
  /// as Inductive with named fields rather than Record, since Rocq rejects
  /// recursive Records outright.
  ///
  /// Crane translates record-shaped inductives to a plain struct with the
  /// fields inlined as members, which is right for non-recursive records but
  /// wrong here: the kids member is emitted as List<cell> kids; inside
  /// struct cell, i.e. the struct is used by value in its own definition,
  /// before its closing brace. That is an incomplete type and does not
  /// compile. The non-record spelling of the same type
  /// (Inductive cell := MkCell : nat -> list cell -> cell) is fine, because
  /// the recursive field goes behind a shared_ptr.
  struct cell {
    uint64_t key;
    List<cell> kids;
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, List<cell> &>
  static T1 cell_rect(F0 &&f, const cell &c) {
    uint64_t key0 = c.key;
    List<cell> kids0 = c.kids;
    return f(key0, kids0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, List<cell> &>
  static T1 cell_rec(F0 &&f, const cell &c) {
    uint64_t key0 = c.key;
    List<cell> kids0 = c.kids;
    return f(key0, kids0);
  }

  static uint64_t csum(const cell &c);
  static uint64_t run(uint64_t n);
};

#endif // INCLUDED_RECURSIVE_RECORD_INCOMPLETE_TYPE
