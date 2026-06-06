#ifndef INCLUDED_CUSTOM_INLINE_BUG
#define INCLUDED_CUSTOM_INLINE_BUG

#include <any>
#include <memory>
#include <optional>
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

struct CustomInlineBug {
  struct State {
    uint64_t value;
    uint64_t data;
  };

  static std::optional<uint64_t> bug_some_proj(const State &s);
  static std::pair<State, uint64_t> bug_pair_proj(State s);
  static std::optional<std::optional<uint64_t>>
  bug_nested_option(const State &s);
  static std::optional<std::pair<State, uint64_t>> bug_option_pair(State s);
  static State get_state(uint64_t n);
  static std::optional<uint64_t> bug_some_of_call(uint64_t n);
  static std::pair<State, uint64_t> pair_simple(State s);
  static std::pair<State, uint64_t> pair_let(uint64_t n);
  static std::pair<std::pair<State, uint64_t>, std::pair<uint64_t, uint64_t>>
  pair_nested(State s);
  static std::pair<State, uint64_t> pair_if(bool b, State s);
  static std::optional<std::pair<State, uint64_t>>
  pair_match(const std::optional<State> &o);
  static std::pair<std::pair<State, uint64_t>, uint64_t>
  pair_multi_proj(State s);
  static std::pair<State, uint64_t> pair_chain(const State &s1);
  static std::pair<std::pair<State, State>, std::pair<uint64_t, uint64_t>>
  pair_extreme(State s);
  static std::pair<State, uint64_t> make_pair(State s);
  static std::pair<State, uint64_t> outer_pair(uint64_t n);
  static List<std::pair<State, uint64_t>> count_pairs(uint64_t n, State s);
};

#endif // INCLUDED_CUSTOM_INLINE_BUG
