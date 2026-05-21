#ifndef INCLUDED_DEP_RECORD
#define INCLUDED_DEP_RECORD

#include <any>
#include <concepts>
#include <memory>
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
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_shared<List<A>>() : nullptr};
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
      this->v_ = Cons{A(a), l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack{};
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

template <typename I>
concept Magma = requires(typename I::carrier a0, typename I::carrier a1) {
  typename I::carrier;
  { I::op(a0, a1) } -> std::convertible_to<typename I::carrier>;
};
template <typename I>concept Monoid = requires (typename I::m_carrier a0,
typename I::m_carrier a1) {
  typename I::m_carrier;
  { I::m_op(a0,
a1) } -> std::convertible_to<typename I::m_carrier>;
} && (requires {
  { I::m_id() } -> std::convertible_to<typename I::m_carrier>;
} || requires {
  { I::m_id } -> std::convertible_to<typename I::m_carrier>;
});

struct DepRecord {
  using carrier = std::any;

  struct nat_magma {
    using carrier = uint64_t;

    static uint64_t op(uint64_t a0, uint64_t a1) { return (a0 + a1); }
  };

  static_assert(Magma<nat_magma>);

  struct bool_magma {
    using carrier = bool;

    constexpr static bool op(bool a0, bool a1) { return (a0 && a1); }
  };

  static_assert(Magma<bool_magma>);
  using m_carrier = std::any;

  struct nat_monoid {
    using m_carrier = uint64_t;

    static uint64_t m_op(uint64_t a0, uint64_t a1) { return (a0 + a1); }

    static uint64_t m_id() { return UINT64_C(0); }
  };

  static_assert(Monoid<nat_monoid>);

  struct nat_mul_monoid {
    using m_carrier = uint64_t;

    static uint64_t m_op(uint64_t a0, uint64_t a1) { return (a0 * a1); }

    static uint64_t m_id() { return UINT64_C(1); }
  };

  static_assert(Monoid<nat_mul_monoid>);

  template <Monoid _tcI0>
  static typename _tcI0::m_carrier
  mfold(const List<typename _tcI0::m_carrier> &l) {
    if (std::holds_alternative<typename List<typename _tcI0::m_carrier>::Nil>(
            l.v())) {
      return _tcI0::m_id();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<typename _tcI0::m_carrier>::Cons>(l.v());
      return _tcI0::m_op(a0, mfold<_tcI0>(*a1));
    }
  }

  static inline const uint64_t test_fold_add =
      std::any_cast<uint64_t>(mfold<nat_monoid>(List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(
                  UINT64_C(3),
                  List<uint64_t>::cons(UINT64_C(4), List<uint64_t>::nil()))))));
  static inline const uint64_t test_fold_mul =
      std::any_cast<uint64_t>(mfold<nat_mul_monoid>(List<uint64_t>::cons(
          UINT64_C(2),
          List<uint64_t>::cons(
              UINT64_C(3),
              List<uint64_t>::cons(UINT64_C(4), List<uint64_t>::nil())))));
  enum class Tag { TNAT, TBOOL };

  template <typename T1> static T1 tag_rect(T1 f, T1 f0, Tag t) {
    switch (t) {
    case Tag::TNAT: {
      return f;
    }
    case Tag::TBOOL: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 tag_rec(T1 f, T1 f0, Tag t) {
    switch (t) {
    case Tag::TNAT: {
      return f;
    }
    case Tag::TBOOL: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  using tag_type = std::any;

  struct Tagged {
    Tag the_tag;
    tag_type the_value;

    // ACCESSORS
    Tagged clone() const { return Tagged{this->the_tag, this->the_value}; }
  };

  static inline const Tagged tagged_nat = Tagged{Tag::TNAT, UINT64_C(42)};
  static inline const Tagged tagged_bool = Tagged{Tag::TBOOL, true};
};

#endif // INCLUDED_DEP_RECORD
