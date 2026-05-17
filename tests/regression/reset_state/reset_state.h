#ifndef INCLUDED_RESET_STATE
#define INCLUDED_RESET_STATE

#include <memory>
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

  unsigned int length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return ((*a1).length() + 1);
    }
  }
};

struct ListDef {
  template <typename T1>
  static T1 nth(unsigned int n, const List<T1> &l, T1 default0);
};

struct ResetState {
  struct state_full {
    unsigned int acc;
    List<unsigned int> regs_full;
    bool carry;
    unsigned int pc_full;
    List<unsigned int> stack;
    List<unsigned int> ram_sys;
    List<unsigned int> rom;

    // ACCESSORS
    state_full clone() const {
      return state_full{(*this).acc,           (*this).regs_full.clone(),
                        (*this).carry,         (*this).pc_full,
                        (*this).stack.clone(), (*this).ram_sys.clone(),
                        (*this).rom.clone()};
    }
  };

  struct state_minimal {
    List<unsigned int> regs_minimal;
    bool carry_minimal;
    unsigned int pc_minimal;
    List<unsigned int> ram_sys_minimal;
    List<unsigned int> rom_minimal;

    // ACCESSORS
    state_minimal clone() const {
      return state_minimal{(*this).regs_minimal.clone(), (*this).carry_minimal,
                           (*this).pc_minimal, (*this).ram_sys_minimal.clone(),
                           (*this).rom_minimal.clone()};
    }
  };

  static state_full reset_state_full(const state_full &s);
  static inline const unsigned int memory_preserve_test = []() {
    state_full s = state_full{
        9u,
        List<unsigned int>::cons(
            1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())),
        true,
        55u,
        List<unsigned int>::cons(
            8u, List<unsigned int>::cons(7u, List<unsigned int>::nil())),
        List<unsigned int>::cons(
            3u,
            List<unsigned int>::cons(
                4u, List<unsigned int>::cons(5u, List<unsigned int>::nil()))),
        List<unsigned int>::cons(
            10u, List<unsigned int>::cons(11u, List<unsigned int>::nil()))};
    state_full s_ = reset_state_full(std::move(s));
    return (
        ((s_.acc + ListDef::template nth<unsigned int>(1u, s_.ram_sys, 0u)) +
         ListDef::template nth<unsigned int>(0u, s_.rom, 0u)) +
        s_.stack.length());
  }();
  static state_minimal reset_state_minimal(const state_minimal &s);
  static inline const unsigned int pc_clear_test =
      reset_state_minimal(
          state_minimal{
              List<unsigned int>::cons(
                  1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())),
              true, 99u,
              List<unsigned int>::cons(3u, List<unsigned int>::nil()),
              List<unsigned int>::cons(
                  4u, List<unsigned int>::cons(5u, List<unsigned int>::nil()))})
          .pc_minimal;
  static inline const std::pair<unsigned int, unsigned int> t =
      std::make_pair(memory_preserve_test, pc_clear_test);
};

template <typename T1>
T1 ListDef::nth(unsigned int n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, default0);
    }
  }
}

#endif // INCLUDED_RESET_STATE
