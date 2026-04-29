#ifndef INCLUDED_FOLD_SEQUENCE_STATE_TRACE
#define INCLUDED_FOLD_SEQUENCE_STATE_TRACE

#include <crane_real.h>
#include <cstdint>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }
};

struct FoldSequenceStateTraceCase {
  using Point = std::pair<Real, Real>;

  struct Line {
    Real A;
    Real B;
    Real C;

    // ACCESSORS
    __attribute__((pure)) Line clone() const {
      return Line{(*(this)).A, (*(this)).B, (*(this)).C};
    }
  };

  struct Fold {
    // TYPES
    struct Fold_line_ctor {
      Line d_a0;
    };

    using variant_t = std::variant<Fold_line_ctor>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Fold() {}

    explicit Fold(Fold_line_ctor _v) : d_v_(std::move(_v)) {}

    Fold(const Fold &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Fold(Fold &&_other) : d_v_(std::move(_other.d_v_)) {}

    Fold &operator=(const Fold &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Fold &operator=(Fold &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) Fold clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<Fold_line_ctor>(_sv.v());
      return Fold(Fold_line_ctor{d_a0.clone()});
    }

    // CREATORS
    __attribute__((pure)) static Fold fold_line_ctor(Line a0) {
      return Fold(Fold_line_ctor{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) Line fold_line() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<typename Fold::Fold_line_ctor>(_sv.v());
      return d_a0;
    }

    template <typename T1, MapsTo<T1, Line> F0> T1 Fold_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<typename Fold::Fold_line_ctor>(_sv.v());
      return f(d_a0);
    }

    template <typename T1, MapsTo<T1, Line> F0> T1 Fold_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<typename Fold::Fold_line_ctor>(_sv.v());
      return f(d_a0);
    }
  };

  static inline const Line line_xaxis =
      Line{Real::from_z(INT64_C(0)), Real::from_z(INT64_C(1)),
           Real::from_z(INT64_C(0))};
  static inline const Line line_yaxis =
      Line{Real::from_z(INT64_C(1)), Real::from_z(INT64_C(0)),
           Real::from_z(INT64_C(0))};
  static inline const Point point_O =
      std::make_pair(Real::from_z(INT64_C(0)), Real::from_z(INT64_C(0)));
  static inline const Point point_X =
      std::make_pair(Real::from_z(INT64_C(1)), Real::from_z(INT64_C(0)));
  static inline const Point point_diag =
      std::make_pair(Real::from_z(INT64_C(1)), Real::from_z(INT64_C(1)));
  __attribute__((pure)) static Line
  line_through(const std::pair<Real, Real> &p1,
               const std::pair<Real, Real> &p2);
  __attribute__((pure)) static Line
  perp_bisector(const std::pair<Real, Real> &p1,
                const std::pair<Real, Real> &p2);
  __attribute__((pure)) static Line perp_through(const std::pair<Real, Real> &p,
                                                 const Line &l);
  __attribute__((pure)) static Fold fold_O1(const std::pair<Real, Real> &p1,
                                            const std::pair<Real, Real> &p2);
  __attribute__((pure)) static Fold fold_O2(const std::pair<Real, Real> &p1,
                                            const std::pair<Real, Real> &p2);
  __attribute__((pure)) static Fold fold_O4(const std::pair<Real, Real> &p,
                                            const Line &l);

  struct FoldStep {
    // TYPES
    struct FS_O1 {
      Point d_a0;
      Point d_a1;
    };

    struct FS_O2 {
      Point d_a0;
      Point d_a1;
    };

    struct FS_O4 {
      Point d_a0;
      Line d_a1;
    };

    using variant_t = std::variant<FS_O1, FS_O2, FS_O4>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    FoldStep() {}

    explicit FoldStep(FS_O1 _v) : d_v_(std::move(_v)) {}

    explicit FoldStep(FS_O2 _v) : d_v_(std::move(_v)) {}

    explicit FoldStep(FS_O4 _v) : d_v_(std::move(_v)) {}

    FoldStep(const FoldStep &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    FoldStep(FoldStep &&_other) : d_v_(std::move(_other.d_v_)) {}

    FoldStep &operator=(const FoldStep &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    FoldStep &operator=(FoldStep &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) FoldStep clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<FS_O1>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<FS_O1>(_sv.v());
        return FoldStep(FS_O1{d_a0, d_a1});
      } else if (std::holds_alternative<FS_O2>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<FS_O2>(_sv.v());
        return FoldStep(FS_O2{d_a0, d_a1});
      } else {
        const auto &[d_a0, d_a1] = std::get<FS_O4>(_sv.v());
        return FoldStep(FS_O4{d_a0, d_a1.clone()});
      }
    }

    // CREATORS
    __attribute__((pure)) static FoldStep fs_o1(Point a0, Point a1) {
      return FoldStep(FS_O1{std::move(a0), std::move(a1)});
    }

    __attribute__((pure)) static FoldStep fs_o2(Point a0, Point a1) {
      return FoldStep(FS_O2{std::move(a0), std::move(a1)});
    }

    __attribute__((pure)) static FoldStep fs_o4(Point a0, Line a1) {
      return FoldStep(FS_O4{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) Line execute_fold_step() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename FoldStep::FS_O1>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename FoldStep::FS_O1>(_sv.v());
        return fold_O1(d_a0, d_a1).fold_line();
      } else if (std::holds_alternative<typename FoldStep::FS_O2>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename FoldStep::FS_O2>(_sv.v());
        return fold_O2(d_a0, d_a1).fold_line();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename FoldStep::FS_O4>(_sv.v());
        return fold_O4(d_a0, d_a1).fold_line();
      }
    }
  };

  template <typename T1,
            MapsTo<T1, std::pair<Real, Real>, std::pair<Real, Real>> F0,
            MapsTo<T1, std::pair<Real, Real>, std::pair<Real, Real>> F1,
            MapsTo<T1, std::pair<Real, Real>, Line> F2>
  static T1 FoldStep_rect(F0 &&f, F1 &&f0, F2 &&f1, const FoldStep &f2) {
    if (std::holds_alternative<typename FoldStep::FS_O1>(f2.v())) {
      const auto &[d_a0, d_a1] = std::get<typename FoldStep::FS_O1>(f2.v());
      return f(d_a0, d_a1);
    } else if (std::holds_alternative<typename FoldStep::FS_O2>(f2.v())) {
      const auto &[d_a0, d_a1] = std::get<typename FoldStep::FS_O2>(f2.v());
      return f0(d_a0, d_a1);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename FoldStep::FS_O4>(f2.v());
      return f1(d_a0, d_a1);
    }
  }

  template <typename T1,
            MapsTo<T1, std::pair<Real, Real>, std::pair<Real, Real>> F0,
            MapsTo<T1, std::pair<Real, Real>, std::pair<Real, Real>> F1,
            MapsTo<T1, std::pair<Real, Real>, Line> F2>
  static T1 FoldStep_rec(F0 &&f, F1 &&f0, F2 &&f1, const FoldStep &f2) {
    if (std::holds_alternative<typename FoldStep::FS_O1>(f2.v())) {
      const auto &[d_a0, d_a1] = std::get<typename FoldStep::FS_O1>(f2.v());
      return f(d_a0, d_a1);
    } else if (std::holds_alternative<typename FoldStep::FS_O2>(f2.v())) {
      const auto &[d_a0, d_a1] = std::get<typename FoldStep::FS_O2>(f2.v());
      return f0(d_a0, d_a1);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename FoldStep::FS_O4>(f2.v());
      return f1(d_a0, d_a1);
    }
  }

  using FoldSequence = List<FoldStep>;

  struct ConstructionState {
    List<Point> state_points;
    List<Line> state_lines;

    // ACCESSORS
    __attribute__((pure)) ConstructionState clone() const {
      return ConstructionState{(*(this)).state_points.clone(),
                               (*(this)).state_lines.clone()};
    }
  };

  static inline const ConstructionState initial_state = ConstructionState{
      List<std::pair<Real, Real>>::cons(
          point_O, List<std::pair<Real, Real>>::cons(
                       point_X, List<std::pair<Real, Real>>::nil())),
      List<Line>::cons(line_xaxis,
                       List<Line>::cons(line_yaxis, List<Line>::nil()))};
  __attribute__((pure)) static ConstructionState
  add_fold_to_state(const ConstructionState &st, const FoldStep &step);
  __attribute__((pure)) static ConstructionState
  execute_sequence(ConstructionState st, const List<FoldStep> &seq);
  static inline const FoldSequence sample_sequence = List<FoldStep>::cons(
      FoldStep::fs_o1(point_O, point_diag),
      List<FoldStep>::cons(
          FoldStep::fs_o2(point_O, point_X),
          List<FoldStep>::cons(FoldStep::fs_o4(point_diag, line_xaxis),
                               List<FoldStep>::nil())));
  static inline const ConstructionState sample_final_state =
      execute_sequence(initial_state, sample_sequence);
  __attribute__((pure)) static unsigned int
  line_count_after_sample_sequence(const ConstructionState &st);
  static inline const unsigned int sample_sequence_length =
      sample_sequence.length();
  static inline const unsigned int sample_line_count =
      line_count_after_sample_sequence(initial_state);
  static inline const unsigned int sample_point_count =
      sample_final_state.state_points.length();
  static inline const bool sample_lines_nonempty = !(sample_line_count == 0u);
  static inline const bool sample_has_expected_lines = sample_line_count == 5u;
};

#endif // INCLUDED_FOLD_SEQUENCE_STATE_TRACE
