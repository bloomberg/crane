#ifndef INCLUDED_STM
#define INCLUDED_STM

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <stm_adapter.h>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, (*a1).app(std::move(m)));
    }
  }
};

struct STMDefs {
  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, T1 &>
  static void modifyTVar(stm::TVar<T1> a, F1 &&f);
};

struct stmtest {
  template <typename T1, typename F1>
    requires std::is_invocable_r_v<bool, F1 &, T1 &>
  static T1 readOrRetry(stm::TVar<T1> tv, F1 &&ok) {
    T1 x = stm::readTVar(tv);
    if (ok(x)) {
      return x;
    } else {
      return stm::retry<T1>();
    }
  }

  static uint64_t stm_basic_counter(std::monostate _x);
  static uint64_t io_basic_counter();
  static uint64_t stm_inc(uint64_t x);
  static uint64_t io_inc(uint64_t x);
  static uint64_t stm_add_self(uint64_t x);
  static uint64_t io_add_self(uint64_t x);
  static void stm_enqueue(stm::TVar<List<uint64_t>> q, uint64_t x);
  static uint64_t stm_dequeue(stm::TVar<List<uint64_t>> q);
  static uint64_t stm_tryDequeue(stm::TVar<List<uint64_t>> q, uint64_t dflt);
  static uint64_t stm_queue_roundtrip(uint64_t x);
  static uint64_t io_queue_roundtrip(uint64_t x);
  static uint64_t stm_orElse_retry_example(std::monostate _x);
  static uint64_t io_orElse_retry_example();
};

template <typename T1, typename F1>
  requires std::is_invocable_r_v<T1, F1 &, T1 &>
void STMDefs::modifyTVar(stm::TVar<T1> a, F1 &&f) {
  T1 val = stm::readTVar(a);
  stm::writeTVar(a, f(val));
  return;
}

#endif // INCLUDED_STM
