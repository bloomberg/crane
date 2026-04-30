#ifndef INCLUDED_DEP_RECORD
#define INCLUDED_DEP_RECORD

#include <any>
#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
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

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

template <typename I>
concept Magma = requires(typename I::carrier a0, typename I::carrier a1) {
  typename I::carrier;
  { I::op(a0, a1) } -> std::convertible_to<typename I::carrier>;
};
template <typename I>
concept Monoid = requires (typename I::m_carrier a0, typename I::m_carrier
a1) {
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
    using carrier = unsigned int;

    static unsigned int op(unsigned int a0, unsigned int a1) {
      return (a0 + a1);
    }
  };

  static_assert(Magma<nat_magma>);

  struct bool_magma {
    using carrier = bool;

    static bool op(bool a0, bool a1) { return (a0 && a1); }
  };

  static_assert(Magma<bool_magma>);
  using m_carrier = std::any;

  struct nat_monoid {
    using m_carrier = unsigned int;

    static unsigned int m_op(unsigned int a0, unsigned int a1) {
      return (a0 + a1);
    }

    static unsigned int m_id() { return 0u; }
  };

  static_assert(Monoid<nat_monoid>);

  struct nat_mul_monoid {
    using m_carrier = unsigned int;

    static unsigned int m_op(unsigned int a0, unsigned int a1) {
      return (a0 * a1);
    }

    static unsigned int m_id() { return 1u; }
  };

  static_assert(Monoid<nat_mul_monoid>);

  template <Monoid _tcI0>
  static typename _tcI0::m_carrier
  mfold(const List<typename _tcI0::m_carrier> &l) {
    if (std::holds_alternative<typename List<typename _tcI0::m_carrier>::Nil>(
            l.v())) {
      return _tcI0::m_id();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<typename _tcI0::m_carrier>::Cons>(l.v());
      return _tcI0::m_op(d_a0, mfold<_tcI0>(*(d_a1)));
    }
  }

  static inline const unsigned int test_fold_add =
      std::any_cast<unsigned int>(mfold<nat_monoid>(List<unsigned int>::cons(
          1u, List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(
                          3u, List<unsigned int>::cons(
                                  4u, List<unsigned int>::nil()))))));
  static inline const unsigned int test_fold_mul = std::any_cast<unsigned int>(
      mfold<nat_mul_monoid>(List<unsigned int>::cons(
          2u,
          List<unsigned int>::cons(
              3u, List<unsigned int>::cons(4u, List<unsigned int>::nil())))));
  enum class Tag { e_TNAT, e_TBOOL };

  template <typename T1>
  static T1 tag_rect(const T1 f, const T1 f0, const Tag t) {
    switch (t) {
    case Tag::e_TNAT: {
      return f;
    }
    case Tag::e_TBOOL: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 tag_rec(const T1 f, const T1 f0, const Tag t) {
    switch (t) {
    case Tag::e_TNAT: {
      return f;
    }
    case Tag::e_TBOOL: {
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
    Tagged clone() const {
      return Tagged{(*(this)).the_tag, (*(this)).the_value};
    }
  };

  static inline const Tagged tagged_nat = Tagged{Tag::e_TNAT, 42u};
  static inline const Tagged tagged_bool = Tagged{Tag::e_TBOOL, true};
};

#endif // INCLUDED_DEP_RECORD
