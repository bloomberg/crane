#ifndef INCLUDED_SUPERFLUOUS_MOVES
#define INCLUDED_SUPERFLUOUS_MOVES

#include <any>
#include <memory>
#include <utility>
#include <variant>

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
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct SuperfluousMoves {
  /// Tiny position record so projections become shared-pointer field accesses.
  struct position {
    uint64_t px;

    // ACCESSORS
    position clone() const { return position{this->px}; }
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

  template <typename T1> static T1 mode_rec(T1 f, T1 f0, Mode m) {
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

  /// Minimal source state carrying the projected fields that trigger the bug.
  struct game_state {
    position pacpos;
    List<position> ghosts;
    uint64_t lives;

    // ACCESSORS
    game_state clone() const {
      return game_state{this->pacpos, this->ghosts, this->lives};
    }
  };

  /// Reduced loop state with only the three fields relevant to the bug.
  struct loop_state {
    game_state ls_game;
    position ls_prev_pac;
    List<position> ls_prev_ghosts;

    // ACCESSORS
    loop_state clone() const {
      return loop_state{this->ls_game, this->ls_prev_pac, this->ls_prev_ghosts};
    }
  };

  /// Identity tick so the reproducer stays minimal while keeping the same
  /// shape.
  static game_state tick(game_state gs);
  /// Life loss used to create the branch-local gs3 value.
  static game_state lose_one_life(const game_state &gs);
  /// Forces the same control-flow path as the original bug.
  static inline const Mode forced_mode = Mode::CHASE;
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
  static std::pair<bool, loop_state> bad_branch(loop_state ls);
};

#endif // INCLUDED_SUPERFLUOUS_MOVES
