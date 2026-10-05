#ifndef INCLUDED_SUPERFLUOUS_MOVES
#define INCLUDED_SUPERFLUOUS_MOVES

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
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
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

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

struct SuperfluousMoves {
  /// Tiny position record so projections become shared-pointer field accesses.
  struct position {
    uint64_t px;
  };
  /// Small mode enum to force a switch in the extracted C++.
  enum class Mode { CHASE, FRIGHTENED };

  template <typename T1> static T1 mode_rect(T1 f, T1 f0, Mode m) {
    switch (m) {
    case Mode::CHASE: {
      return f;
    }
    case Mode::FRIGHTENED: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 mode_rec(const T1 &f, const T1 &f0, Mode m) {
    return mode_rect<T1>(f, f0, m);
  }

  /// Minimal source state carrying the projected fields that trigger the bug.
  struct game_state {
    position pacpos;
    List<position> ghosts;
    uint64_t lives;
  };

  /// Reduced loop state with only the three fields relevant to the bug.
  struct loop_state {
    game_state ls_game;
    position ls_prev_pac;
    List<position> ls_prev_ghosts;
  };

  /// Identity tick so the reproducer stays minimal while keeping the same
  /// shape.
  static game_state tick(game_state gs);
  /// Life loss used to create the branch-local gs3 value.
  static game_state lose_one_life(const game_state &gs);
  /// Forces the same control-flow path as the original bug.
  static constexpr Mode forced_mode = Mode::CHASE;
  /// Concrete state that makes the game-over branch fire after lose_one_life.
  static inline const game_state sample_state = game_state{
      position{UINT64_C(7)},
      List<position>::cons(
          position{UINT64_C(1)},
          List<position>::cons(position{UINT64_C(2)}, List<position>::nil())),
      UINT64_C(1)};
  /// Concrete loop state used by the standalone entrypoint.
  static inline const loop_state sample_loop =
      loop_state{sample_state, sample_state.pacpos, sample_state.ghosts};
  /// Reduced branch reproducer without the outer option * nat wrapper.
  static std::pair<bool, loop_state> bad_branch(const loop_state &ls);
};

#endif // INCLUDED_SUPERFLUOUS_MOVES
