#ifndef INCLUDED_LOOPIFY_NUMERIC_SEQUENCES
#define INCLUDED_LOOPIFY_NUMERIC_SEQUENCES

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

  template <typename _U> explicit List(const List<_U> &_other) {
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
    std::vector<std::shared_ptr<List<A>>> _stack = {};
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
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct LoopifyNumericSequences {
  static uint64_t collatz_length_fuel(uint64_t fuel, uint64_t n);
  static uint64_t collatz_length(uint64_t n);
  static List<uint64_t> collatz_sequence_fuel(uint64_t fuel, uint64_t n);
  static List<uint64_t> collatz_sequence(uint64_t n);
  static uint64_t tribonacci_fuel(uint64_t fuel, uint64_t n);
  static uint64_t tribonacci(uint64_t n);
  static uint64_t staircase_fuel(uint64_t fuel, uint64_t n);
  static uint64_t staircase(uint64_t n);

  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static uint64_t church(uint64_t n, F1 &&f, uint64_t x) {
    uint64_t _loop_x = std::move(x);
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        return _loop_x;
      } else {
        uint64_t n_ = _loop_n - 1;
        _loop_x = f(_loop_x);
        _loop_n = n_;
      }
    }
  }

  static uint64_t digitsum_fuel(uint64_t fuel, uint64_t n);
  static uint64_t digitsum(uint64_t n);
  static uint64_t dec_to_bin_fuel(uint64_t fuel, uint64_t n);
  static uint64_t dec_to_bin(uint64_t n);
  static uint64_t alternate_sum(bool sign, uint64_t acc,
                                const List<uint64_t> &l);
  static uint64_t sum_divisors_aux(uint64_t n, uint64_t d);
  static uint64_t sum_divisors(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_NUMERIC_SEQUENCES
