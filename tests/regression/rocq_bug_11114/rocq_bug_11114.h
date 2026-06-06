#ifndef INCLUDED_ROCQ_BUG_11114
#define INCLUDED_ROCQ_BUG_11114

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

struct RocqBug11114 {
  struct t {
    // DATA
    uint64_t k;

    // ACCESSORS
    t clone() const { return {k}; }

    // CREATORS
    static t t0(uint64_t k) { return {k}; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 t_rect(const List<uint64_t> &, F1 &&f, const t &t0) {
    const auto &[k0] = t0;
    return f(k0);
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 t_rec(const List<uint64_t> &, F1 &&f, const t &t0) {
    const auto &[k0] = t0;
    return f(k0);
  }

  struct pkg {
    List<uint64_t> _sig;
    t _t;
  };

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static pkg map(F0 &&f, const pkg &p) {
    return pkg{p._sig, [=]() mutable {
                 const auto &_sv = p._t;
                 const auto &[k0] = _sv;
                 return t::t0(f(k0));
               }()};
  }

  static inline const pkg test_pkg =
      pkg{List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil()),
          t::t0(UINT64_C(2))};
  static inline const pkg test_map =
      map([](uint64_t x) { return (x + UINT64_C(1)); }, test_pkg);
};

#endif // INCLUDED_ROCQ_BUG_11114
