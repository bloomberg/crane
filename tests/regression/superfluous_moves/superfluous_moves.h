#ifndef INCLUDED_SUPERFLUOUS_MOVES
#define INCLUDED_SUPERFLUOUS_MOVES

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct SuperfluousMoves {
  /// Tiny position record so projections become shared-pointer field accesses.
  struct position {
    unsigned int px;
  };
  /// Small mode enum to force a switch in the extracted C++.
  enum class Mode { e_CHASE, e_FRIGHTENED };

  template <typename T1>
  static T1 mode_rect(const T1 f, const T1 f0, const Mode m) {
    switch (m) {
    case Mode::e_CHASE: {
      return f;
    }
    case Mode::e_FRIGHTENED: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 mode_rec(const T1 f, const T1 f0, const Mode m) {
    switch (m) {
    case Mode::e_CHASE: {
      return f;
    }
    case Mode::e_FRIGHTENED: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  /// Minimal source state carrying the projected fields that trigger the bug.
  struct game_state {
    std::shared_ptr<position> pacpos;
    std::shared_ptr<List<std::shared_ptr<position>>> ghosts;
    unsigned int lives;
  };

  /// Reduced loop state with only the three fields relevant to the bug.
  struct loop_state {
    std::shared_ptr<game_state> ls_game;
    std::shared_ptr<position> ls_prev_pac;
    std::shared_ptr<List<std::shared_ptr<position>>> ls_prev_ghosts;
  };

  /// Identity tick so the reproducer stays minimal while keeping the same
  /// shape.
  static std::shared_ptr<game_state> tick(std::shared_ptr<game_state> gs);
  /// Life loss used to create the branch-local gs3 value.
  static std::shared_ptr<game_state>
  lose_one_life(const std::shared_ptr<game_state> &gs);
  /// Forces the same control-flow path as the original bug.
  static inline const Mode forced_mode = Mode::e_CHASE;
  /// Concrete state that makes the game-over branch fire after lose_one_life.
  static inline const std::shared_ptr<game_state> sample_state =
      std::make_shared<game_state>(
          game_state{std::make_shared<position>(position{7u}),
                     List<std::shared_ptr<position>>::cons(
                         std::make_shared<position>(position{1u}),
                         List<std::shared_ptr<position>>::cons(
                             std::make_shared<position>(position{2u}),
                             List<std::shared_ptr<position>>::nil())),
                     1u});
  /// Concrete loop state used by the standalone entrypoint.
  static inline const std::shared_ptr<loop_state> sample_loop =
      std::make_shared<loop_state>(
          loop_state{sample_state, sample_state->pacpos, sample_state->ghosts});
  /// Reduced branch reproducer without the outer option * nat wrapper.
  __attribute__((pure)) static std::pair<bool, std::shared_ptr<loop_state>>
  bad_branch(std::shared_ptr<loop_state> ls);
};

#endif // INCLUDED_SUPERFLUOUS_MOVES
