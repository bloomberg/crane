#ifndef INCLUDED_DOUBLE_TYPENAME
#define INCLUDED_DOUBLE_TYPENAME

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

template <typename M>
concept OrderedType = requires { typename M::t; };

struct DoubleTypename {
  template <OrderedType X> struct MakeMap {
    template <typename A> struct entry {
      // DATA
      typename X::t a0;
      A a1;

      // ACCESSORS
      entry<A> clone() const { return {a0, a1}; }

      // CREATORS
      static entry<A> entry0(typename X::t a0, A a1) {
        return {std::move(a0), std::move(a1)};
      }
    };

    template <typename T1, typename T2, typename F0>
      requires std::is_invocable_r_v<T2, F0 &, typename X::t &, T1 &>
    static T2 entry_rect(F0 &&f, const entry<T1> &e) {
      const auto &[a0, a1] = e;
      return f(a0, a1);
    }

    template <typename T1, typename T2, typename F0>
      requires std::is_invocable_r_v<T2, F0 &, typename X::t &, T1 &>
    static T2 entry_rec(F0 &&f, const entry<T1> &e) {
      const auto &[a0, a1] = e;
      return f(a0, a1);
    }

    template <typename T1>
    static List<typename X::t> keys(const List<entry<T1>> &l) {
      if (std::holds_alternative<typename List<entry<T1>>::Nil>(l.v())) {
        return List<typename X::t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<entry<T1>>::Cons>(l.v());
        const auto &[a00, a10] = a0;
        return List<typename X::t>::cons(a00, List<typename X::t>::nil());
      }
    }
  };

  struct NatOrd {
    using t = uint64_t;
  };

  using NatMap = MakeMap<NatOrd>;
  static inline const List<uint64_t> test =
      NatMap::template keys<uint64_t>(List<NatMap::entry<uint64_t>>::cons(
          NatMap::template entry<uint64_t>::entry0(UINT64_C(1), UINT64_C(2)),
          List<NatMap::entry<uint64_t>>::nil()));
};

#endif // INCLUDED_DOUBLE_TYPENAME
