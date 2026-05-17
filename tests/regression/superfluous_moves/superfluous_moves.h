#ifndef INCLUDED_SUPERFLUOUS_MOVES
#define INCLUDED_SUPERFLUOUS_MOVES

#include <memory>
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

struct SuperfluousMoves {
  /// Tiny position record so projections become shared-pointer field accesses.
  struct position {
    unsigned int px;

    // ACCESSORS
    position clone() const { return position{(*this).px}; }
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
    unsigned int lives;

    // ACCESSORS
    game_state clone() const {
      return game_state{(*this).pacpos.clone(), (*this).ghosts.clone(),
                        (*this).lives};
    }
  };

  /// Reduced loop state with only the three fields relevant to the bug.
  struct loop_state {
    game_state ls_game;
    position ls_prev_pac;
    List<position> ls_prev_ghosts;

    // ACCESSORS
    loop_state clone() const {
      return loop_state{(*this).ls_game.clone(), (*this).ls_prev_pac.clone(),
                        (*this).ls_prev_ghosts.clone()};
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
  static inline const game_state sample_state =
      game_state{position{7u},
                 List<position>::cons(
                     position{1u},
                     List<position>::cons(position{2u}, List<position>::nil())),
                 1u};
  /// Concrete loop state used by the standalone entrypoint.
  static inline const loop_state sample_loop =
      loop_state{sample_state, sample_state.pacpos, sample_state.ghosts};
  /// Reduced branch reproducer without the outer option * nat wrapper.
  static std::pair<bool, loop_state> bad_branch(loop_state ls);
};

#endif // INCLUDED_SUPERFLUOUS_MOVES
