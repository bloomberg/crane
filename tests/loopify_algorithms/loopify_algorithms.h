#ifndef INCLUDED_LOOPIFY_ALGORITHMS
#define INCLUDED_LOOPIFY_ALGORITHMS

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
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

  List<A> app(List<A> m) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
};

struct LoopifyAlgorithms {
  static uint64_t len_impl(const List<uint64_t> &l);
  static List<uint64_t> sieve_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> sieve(const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>>
  run_length_encode(const List<uint64_t> &l);
  static List<uint64_t> prefix_sums(uint64_t acc, const List<uint64_t> &l);
  static List<uint64_t> differences(const List<uint64_t> &l);
  static List<uint64_t> rotate_left_fuel(uint64_t fuel, uint64_t n,
                                         List<uint64_t> l);
  static List<uint64_t> rotate_left(uint64_t n, const List<uint64_t> &l);
  static List<uint64_t> nub_aux(const List<uint64_t> &l, uint64_t fuel);
  static List<uint64_t> nub(const List<uint64_t> &l);
  static List<uint64_t> rev_impl(List<uint64_t> acc, const List<uint64_t> &l);
  static bool list_eq_impl(const List<uint64_t> &l1, const List<uint64_t> &l2);
  static bool is_palindrome(const List<uint64_t> &l);
  static List<uint64_t> take_impl(uint64_t k, const List<uint64_t> &l);
  static List<List<uint64_t>> windows_aux(uint64_t n, const List<uint64_t> &l,
                                          uint64_t fuel);
  static List<List<uint64_t>> windows(uint64_t n, const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>>
  sliding_pairs(const List<uint64_t> &l);
  static uint64_t max_prefix_sum(const List<uint64_t> &l);
  static uint64_t weighted_sum(uint64_t i, const List<uint64_t> &l);
  static uint64_t step_sum(const List<uint64_t> &l);
  static uint64_t head_nat(uint64_t d, const List<uint64_t> &l);
  static List<uint64_t> suffix_sums(const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_ALGORITHMS
