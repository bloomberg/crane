#ifndef INCLUDED_LOOPIFY_LIST_ACCESS
#define INCLUDED_LOOPIFY_LIST_ACCESS

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

struct LoopifyListAccess {
  static uint64_t nth(uint64_t n, const List<uint64_t> &l);
  static uint64_t last(const List<uint64_t> &l);
  static uint64_t index_of_aux(uint64_t x, const List<uint64_t> &l,
                               uint64_t idx);
  static uint64_t index_of(uint64_t x, const List<uint64_t> &l);
  static bool member(uint64_t x, const List<uint64_t> &l);
  static uint64_t lookup(uint64_t key,
                         const List<std::pair<uint64_t, uint64_t>> &l);
  static List<uint64_t>
  lookup_all(uint64_t key, const List<std::pair<uint64_t, uint64_t>> &l);

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static uint64_t find(F0 &&p, const List<uint64_t> &l) {
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          return a0;
        } else {
          _loop_l = a1.get();
        }
      }
    }
  }

  static uint64_t count(uint64_t x, const List<uint64_t> &l);

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static uint64_t count_matching(
      F0 &&p,
      const List<uint64_t>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Resume1: saves [_s0], resumes after recursive call with _result.
    struct _Resume1 {
      std::decay_t<decltype(UINT64_C(1))> _s0;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified count_matching: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(_Resume1{UINT64_C(1)});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = (_f._s0 + std::move(_result));
      }
    }
    return _result;
  }

  static bool elem_at_eq(uint64_t idx, uint64_t val, const List<uint64_t> &l);
  static uint64_t nth_default(uint64_t n, uint64_t default0,
                              const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_ACCESS
