#ifndef INCLUDED_LOOPIFY_NUMERIC_SEQUENCES
#define INCLUDED_LOOPIFY_NUMERIC_SEQUENCES

#include <memory>
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
    uint64_t _result;
    uint64_t _loop_x = std::move(x);
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        _result = std::move(_loop_x);
        break;
      } else {
        uint64_t n_ = _loop_n - 1;
        _loop_x = f(_loop_x);
        _loop_n = n_;
      }
    }
    return _result;
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
