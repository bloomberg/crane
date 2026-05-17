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

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
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

template <typename M>
concept OrderedType = requires { typename M::t; };

struct DoubleTypename {
  template <OrderedType X> struct MakeMap {
    template <typename A> struct entry {
      // TYPES
      struct Entry0 {
        typename X::t a0;
        A a1;
      };

      using variant_t = std::variant<Entry0>;

    private:
      // DATA
      variant_t v_;

    public:
      // CREATORS
      entry() {}

      explicit entry(Entry0 _v) : v_(std::move(_v)) {}

      entry(const entry<A> &_other) : v_(std::move(_other.clone().v_)) {}

      entry(entry<A> &&_other) : v_(std::move(_other.v_)) {}

      entry<A> &operator=(const entry<A> &_other) {
        v_ = std::move(_other.clone().v_);
        return *this;
      }

      entry<A> &operator=(entry<A> &&_other) {
        v_ = std::move(_other.v_);
        return *this;
      }

      // ACCESSORS
      entry<A> clone() const {
        const auto &[a0, a1] = std::get<Entry0>(this->v());
        return entry<A>(Entry0{a0, a1});
      }

      // CREATORS
      template <typename _U> explicit entry(const entry<_U> &_other) {
        const auto &[a0, a1] = std::get<typename entry<_U>::Entry0>(_other.v());
        this->v_ = Entry0{a0, A(a1)};
      }

      static entry<A> entry0(typename X::t a0, A a1) {
        return entry(Entry0{std::move(a0), std::move(a1)});
      }

      // MANIPULATORS
      inline variant_t &v_mut() { return v_; }

      // ACCESSORS
      const variant_t &v() const { return v_; }
    };

    template <typename T1, typename T2, typename F0>
      requires std::is_invocable_r_v<T2, F0 &, typename X::t &, T1 &>
    static T2 entry_rect(F0 &&f, const entry<T1> &e) {
      const auto &[a0, a1] = std::get<typename entry<T1>::Entry0>(e.v());
      return f(a0, a1);
    }

    template <typename T1, typename T2, typename F0>
      requires std::is_invocable_r_v<T2, F0 &, typename X::t &, T1 &>
    static T2 entry_rec(F0 &&f, const entry<T1> &e) {
      const auto &[a0, a1] = std::get<typename entry<T1>::Entry0>(e.v());
      return f(a0, a1);
    }

    template <typename T1>
    static List<typename X::t> keys(const List<entry<T1>> &l) {
      if (std::holds_alternative<typename List<entry<T1>>::Nil>(l.v())) {
        return List<typename X::t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<entry<T1>>::Cons>(l.v());
        const auto &[a00, a10] = std::get<typename entry<T1>::Entry0>(a0.v());
        return List<typename X::t>::cons(a00, List<typename X::t>::nil());
      }
    }
  };

  struct NatOrd {
    using t = unsigned int;
  };

  using NatMap = MakeMap<NatOrd>;
  static inline const List<unsigned int> test =
      NatMap::template keys<unsigned int>(
          List<NatMap::entry<unsigned int>>::cons(
              NatMap::template entry<unsigned int>::entry0(1u, 2u),
              List<NatMap::entry<unsigned int>>::nil()));
};

#endif // INCLUDED_DOUBLE_TYPENAME
