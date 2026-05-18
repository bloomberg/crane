#ifndef INCLUDED_PRESERVES_ALL_PAIRS
#define INCLUDED_PRESERVES_ALL_PAIRS

#include <memory>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::unique_ptr<List<A>> l;
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
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
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
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
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

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct PreservesAllPairs {
  struct state {
    List<uint64_t> regs;
    uint64_t acc;

    // ACCESSORS
    state clone() const { return state{(*this).regs.clone(), (*this).acc}; }
  };

  static uint64_t get_reg(const state &s, uint64_t r);
  static uint64_t nibble_of_nat(uint64_t n);
  static uint64_t get_reg_pair(const state &s, uint64_t r);
  static state execute_add(const state &s, uint64_t r);
  static state execute_ld(const state &s, uint64_t r);
  static state execute_sub(const state &s, uint64_t r);
  static inline const state sample =
      state{List<uint64_t>::cons(
                UINT64_C(2),
                List<uint64_t>::cons(
                    UINT64_C(9),
                    List<uint64_t>::cons(
                        UINT64_C(4),
                        List<uint64_t>::cons(
                            UINT64_C(7),
                            List<uint64_t>::cons(
                                UINT64_C(8),
                                List<uint64_t>::cons(
                                    UINT64_C(1), List<uint64_t>::nil())))))),
            UINT64_C(13)};
  static inline const bool add_preserves_pairs =
      get_reg_pair(execute_add(sample, UINT64_C(4)), UINT64_C(2)) ==
      get_reg_pair(sample, UINT64_C(2));
  static inline const bool ld_preserves_pairs =
      get_reg_pair(execute_ld(sample, UINT64_C(4)), UINT64_C(2)) ==
      get_reg_pair(sample, UINT64_C(2));
  static inline const bool sub_preserves_pairs =
      get_reg_pair(execute_sub(sample, UINT64_C(4)), UINT64_C(2)) ==
      get_reg_pair(sample, UINT64_C(2));
  static inline const bool t =
      ((add_preserves_pairs && ld_preserves_pairs) && sub_preserves_pairs);
};

template <typename T1>
T1 ListDef::nth(uint64_t n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, default0);
    }
  }
}

#endif // INCLUDED_PRESERVES_ALL_PAIRS
