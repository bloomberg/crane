#ifndef INCLUDED_CUSTOM_INLINE_BUG
#define INCLUDED_CUSTOM_INLINE_BUG

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

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
  static std::pair<State, uint64_t> bug_pair_proj(const State &s);
  static std::optional<std::optional<uint64_t>>
  bug_nested_option(const State &s);
  static std::optional<std::pair<State, uint64_t>>
  bug_option_pair(const State &s);
  static State get_state(uint64_t n);
  static std::optional<uint64_t> bug_some_of_call(uint64_t n);
  static std::pair<State, uint64_t> pair_simple(const State &s);
  static std::pair<State, uint64_t> pair_let(uint64_t n);
  static std::pair<std::pair<State, uint64_t>, std::pair<uint64_t, uint64_t>>
  pair_nested(const State &s);
  static std::pair<State, uint64_t> pair_if(bool b, const State &s);
  static std::optional<std::pair<State, uint64_t>>
  pair_match(const std::optional<State> &o);
  static std::pair<std::pair<State, uint64_t>, uint64_t>
  pair_multi_proj(const State &s);
  static std::pair<State, uint64_t> pair_chain(const State &s1);
  static std::pair<std::pair<State, State>, std::pair<uint64_t, uint64_t>>
  pair_extreme(const State &s);
  static std::pair<State, uint64_t> make_pair(const State &s);
  static std::pair<State, uint64_t> outer_pair(uint64_t n);
  static List<std::pair<State, uint64_t>> count_pairs(uint64_t n,
                                                      const State &s);
};

#endif // INCLUDED_CUSTOM_INLINE_BUG
