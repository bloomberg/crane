#ifndef INCLUDED_FETCH_OPS
#define INCLUDED_FETCH_OPS

#include <memory>
#include <optional>
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

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct FetchOps {
  struct state {
    List<uint64_t> rom;

    // ACCESSORS
    state clone() const { return state{(*this).rom.clone()}; }
  };

  static uint64_t fetch_byte(const state &s, uint64_t addr);
  static inline const uint64_t fetch_default_test =
      fetch_byte(state{List<uint64_t>::cons(
                     UINT64_C(1),
                     List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil()))},
                 UINT64_C(5));
  static uint64_t fetch_byte_direct(const List<uint64_t> &rom_data,
                                    uint64_t addr);
  static inline const uint64_t fetch_in_range_test = fetch_byte_direct(
      List<uint64_t>::cons(
          UINT64_C(11),
          List<uint64_t>::cons(
              UINT64_C(22),
              List<uint64_t>::cons(UINT64_C(33), List<uint64_t>::nil()))),
      UINT64_C(1));

  template <typename T1> static List<T1> drop(uint64_t n, List<T1> l) {
    if (n <= 0) {
      return l;
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v_mut())) {
        return List<T1>::nil();
      } else {
        auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v_mut());
        return drop<T1>(n_, *a1);
      }
    }
  }

  static std::pair<uint64_t, uint64_t>
  fetch_pair(const List<uint64_t> &rom_data, uint64_t addr);
  static inline const uint64_t fetch_pair_test = []() {
    std::pair<uint64_t, uint64_t> p = fetch_pair(
        List<uint64_t>::cons(
            UINT64_C(1),
            List<uint64_t>::cons(
                UINT64_C(2),
                List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))),
        UINT64_C(0));
    return (p.first + p.second);
  }();
  static std::optional<std::pair<uint64_t, uint64_t>>
  fetch_window(const List<uint64_t> &rom_data, uint64_t addr);
  static inline const uint64_t fetch_window_test = []() -> uint64_t {
    auto _cs = fetch_window(
        List<uint64_t>::cons(
            UINT64_C(9),
            List<uint64_t>::cons(
                UINT64_C(8),
                List<uint64_t>::cons(UINT64_C(7), List<uint64_t>::nil()))),
        UINT64_C(0));
    if (_cs.has_value()) {
      const std::pair<uint64_t, uint64_t> &p = *_cs;
      const uint64_t &_x = p.first;
      const uint64_t &next = p.second;
      return next;
    } else {
      return UINT64_C(0);
    }
  }();
  static inline const std::pair<
      std::pair<std::pair<uint64_t, uint64_t>, uint64_t>, uint64_t>
      t = std::make_pair(std::make_pair(std::make_pair(fetch_default_test,
                                                       fetch_in_range_test),
                                        fetch_pair_test),
                         fetch_window_test);
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

#endif // INCLUDED_FETCH_OPS
