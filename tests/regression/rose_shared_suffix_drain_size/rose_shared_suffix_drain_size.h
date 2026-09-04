#ifndef INCLUDED_ROSE_SHARED_SUFFIX_DRAIN_SIZE
#define INCLUDED_ROSE_SHARED_SUFFIX_DRAIN_SIZE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>)
                          return crane_any_cast<A>(a);
                        else
                          return A(a);
                      }(),
                      (l ? std::make_shared<List<A>>(*l) : nullptr)};
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

/// Same underlying defect as rose_shared_suffix_drain, reached with a
/// different consumer and three successive sharers of the same spine: the
/// generated ~rose() drains the list rose child cell by cell, checking
/// ownership only on the head shared_ptr, so the shared tail cells are
/// left moved-from for the next reader.
struct RoseSharedSuffixDrainSize {
  struct rose {
    // TYPES
    struct Node {
      uint64_t a0;
      std::shared_ptr<List<rose>> a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(Node _v) : v_(std::move(_v)) {}

    static rose node(uint64_t a0, List<rose> a1) {
      return rose(Node{a0, std::make_shared<List<rose>>(std::move(a1))});
    }

    // MANIPULATORS
    ~rose() {
      crane::small_vector<std::shared_ptr<rose>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto _lp = _alt->a1.get();
            while (
                std::holds_alternative<typename List<rose>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<rose>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<rose>(std::move(_lc.a)));
              if (_lc.l && _lc.l.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
            _alt->a1.reset();
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

    rose(const rose &) = default;
    rose &operator=(const rose &) = default;
    rose(rose &&) noexcept = default;
    rose &operator=(rose &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, List<rose> &>
  static T1 rose_rect(F0 &&f, const rose &r) {
    const auto &[a0, a1] = std::get<typename rose::Node>(r.v());
    return f(a0, *a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, List<rose> &>
  static T1 rose_rec(F0 &&f, const rose &r) {
    const auto &[a0, a1] = std::get<typename rose::Node>(r.v());
    return f(a0, *a1);
  }

  static uint64_t rsize(const rose &t);
  static uint64_t run(uint64_t n);
};

#endif // INCLUDED_ROSE_SHARED_SUFFIX_DRAIN_SIZE
