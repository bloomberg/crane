#ifndef INCLUDED_TYPE_APP
#define INCLUDED_TYPE_APP

#include <concepts>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename M>
concept Monoid = requires {
  typename M::T;
  requires(
      requires {
        { M::empty } -> std::convertible_to<typename M::T>;
      } ||
      requires {
        { M::empty() } -> std::convertible_to<typename M::T>;
      });
  {
    M::append(std::declval<typename M::T>(), std::declval<typename M::T>())
  } -> std::same_as<typename M::T>;
};

struct TypeApp {
  template <typename T1> static T1 id(T1 x) { return x; }

  static inline const uint64_t id_int = id<uint64_t>(UINT64_C(42));
  static inline const bool id_bool = id<bool>(true);

  template <typename T1, typename T2 = void, typename T3, typename F0,
            typename F1>
  static T3 compose(F0 &&g, F1 &&f, const T1 &x) {
    return g(f(x));
  }

  template <typename T1> static T1 nested_poly(const T1 &x) {
    return id<T1>(id<T1>(id<T1>(x)));
  }

  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::unique_ptr<list<A>> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    list(const list<A> &_other) : v_(std::move(_other.clone().v_)) {}

    list(list<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    list<A> &operator=(const list<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    list<A> &operator=(list<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    list<A> clone() const {
      list<A> _out{};

      struct _CloneFrame {
        const list<A> *_src;
        list<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const list<A> *_src = _frame._src;
        list<A> *_dst = _frame._dst;
        if (std::holds_alternative<Nil>(_src->v())) {
          _dst->v_ = Nil{};
        } else {
          const auto &_alt = std::get<Cons>(_src->v());
          _dst->v_ =
              Cons{_alt.a0, _alt.a1 ? std::make_unique<list<A>>() : nullptr};
          auto &_dst_alt = std::get<Cons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a0, a1] = std::get<typename list<_U>::Cons>(_other.v());
        this->v_ = Cons{A(a0), a1 ? std::make_unique<list<A>>(*a1) : nullptr};
      }
    }

    static list<A> nil() { return list(Nil{}); }

    static list<A> cons(A a0, list<A> a1) {
      return list(
          Cons{std::move(a0), std::make_unique<list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      std::vector<std::unique_ptr<list<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](list<A> &_node) {
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

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2 list_rect(T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(a0, *a1, list_rect<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2 list_rec(T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(a0, *a1, list_rec<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static list<T2> map(F0 &&f, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return list<T2>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return list<T2>::cons(f(a0), map<T1, T2>(f, *a1));
    }
  }

  static inline const list<uint64_t> test_map = map<uint64_t, uint64_t>(
      [](uint64_t x) { return (x + UINT64_C(1)); },
      list<uint64_t>::cons(
          UINT64_C(1),
          list<uint64_t>::cons(
              UINT64_C(2),
              list<uint64_t>::cons(UINT64_C(3), list<uint64_t>::nil()))));
  static list<uint64_t> map_succ(const list<uint64_t> &_x0);
  static inline const list<uint64_t> test_map_succ =
      map_succ(list<uint64_t>::cons(
          UINT64_C(5),
          list<uint64_t>::cons(UINT64_C(6), list<uint64_t>::nil())));

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &>
  static T1 twice(F0 &&f, const T1 &x) {
    return f(f(x));
  }

  static inline const uint64_t test_twice = twice<uint64_t>(
      [](uint64_t x) { return (x + UINT64_C(1)); }, UINT64_C(10));

  struct NatMonoid {
    using T = uint64_t;
    static inline const uint64_t empty = UINT64_C(0);
    static uint64_t append(uint64_t _x0, uint64_t _x1);
  };

  template <Monoid M> struct UseMonoid {
    static const typename M::T &combine_empty() {
      static const typename M::T v = M::append(M::empty, M::empty);
      return v;
    }

    constexpr static typename M::T triple(typename M::T x) {
      return M::append(x, M::append(x, x));
    }
  };

  using NatMonoidUser = UseMonoid<NatMonoid>;
  static inline const NatMonoid::T monoid_test = NatMonoidUser::combine_empty();
};

#endif // INCLUDED_TYPE_APP
