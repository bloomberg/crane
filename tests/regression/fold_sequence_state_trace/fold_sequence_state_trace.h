#ifndef INCLUDED_FOLD_SEQUENCE_STATE_TRACE
#define INCLUDED_FOLD_SEQUENCE_STATE_TRACE

#include <crane_real.h>
#include <cstdint>
#include <memory>
#include <type_traits>
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

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
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
    Line clone() const { return Line{(*this).A, (*this).B, (*this).C}; }
  };

  struct Fold {
    // DATA
    Line a0;

    // ACCESSORS
    Fold clone() const { return {a0}; }

    // CREATORS
    static Fold fold_line_ctor(Line a0) { return {std::move(a0)}; }

    Line fold_line() const {
      const auto &_sv = *this;
      const auto &[a0] = _sv;
      return a0;
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, Line &>
    T1 Fold_rec(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0] = _sv;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, Line &>
    T1 Fold_rect(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0] = _sv;
      return f(a0);
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
  static Line line_through(const std::pair<Real, Real> &p1,
                           const std::pair<Real, Real> &p2);
  static Line perp_bisector(const std::pair<Real, Real> &p1,
                            const std::pair<Real, Real> &p2);
  static Line perp_through(const std::pair<Real, Real> &p, const Line &l);
  static Fold fold_O1(const std::pair<Real, Real> &p1,
                      const std::pair<Real, Real> &p2);
  static Fold fold_O2(const std::pair<Real, Real> &p1,
                      const std::pair<Real, Real> &p2);
  static Fold fold_O4(const std::pair<Real, Real> &p, const Line &l);

  struct FoldStep {
    // TYPES
    struct FS_O1 {
      Point a0;
      Point a1;
    };

    struct FS_O2 {
      Point a0;
      Point a1;
    };

    struct FS_O4 {
      Point a0;
      Line a1;
    };

    using variant_t = std::variant<FS_O1, FS_O2, FS_O4>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    FoldStep() {}

    explicit FoldStep(FS_O1 _v) : v_(std::move(_v)) {}

    explicit FoldStep(FS_O2 _v) : v_(std::move(_v)) {}

    explicit FoldStep(FS_O4 _v) : v_(std::move(_v)) {}

    FoldStep(const FoldStep &_other) : v_(std::move(_other.clone().v_)) {}

    FoldStep(FoldStep &&_other) noexcept : v_(std::move(_other.v_)) {}

    FoldStep &operator=(const FoldStep &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    FoldStep &operator=(FoldStep &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    FoldStep clone() const {
      if (std::holds_alternative<FS_O1>(this->v())) {
        const auto &[a0, a1] = std::get<FS_O1>(this->v());
        return FoldStep(FS_O1{a0, a1});
      } else if (std::holds_alternative<FS_O2>(this->v())) {
        const auto &[a0, a1] = std::get<FS_O2>(this->v());
        return FoldStep(FS_O2{a0, a1});
      } else {
        const auto &[a0, a1] = std::get<FS_O4>(this->v());
        return FoldStep(FS_O4{a0, a1.clone()});
      }
    }

    // CREATORS
    static FoldStep fs_o1(Point a0, Point a1) {
      return FoldStep(FS_O1{std::move(a0), std::move(a1)});
    }

    static FoldStep fs_o2(Point a0, Point a1) {
      return FoldStep(FS_O2{std::move(a0), std::move(a1)});
    }

    static FoldStep fs_o4(Point a0, Line a1) {
      return FoldStep(FS_O4{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    Line execute_fold_step() const {
      if (std::holds_alternative<typename FoldStep::FS_O1>(this->v())) {
        const auto &[a0, a1] = std::get<typename FoldStep::FS_O1>(this->v());
        return fold_O1(a0, a1).fold_line();
      } else if (std::holds_alternative<typename FoldStep::FS_O2>(this->v())) {
        const auto &[a0, a1] = std::get<typename FoldStep::FS_O2>(this->v());
        return fold_O2(a0, a1).fold_line();
      } else {
        const auto &[a0, a1] = std::get<typename FoldStep::FS_O4>(this->v());
        return fold_O4(a0, a1).fold_line();
      }
    }
  };

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, std::pair<Real, Real> &,
                                   std::pair<Real, Real> &> &&
             std::is_invocable_r_v<T1, F1 &, std::pair<Real, Real> &,
                                   std::pair<Real, Real> &> &&
             std::is_invocable_r_v<T1, F2 &, std::pair<Real, Real> &, Line &>
  static T1 FoldStep_rect(F0 &&f, F1 &&f0, F2 &&f1, const FoldStep &f2) {
    if (std::holds_alternative<typename FoldStep::FS_O1>(f2.v())) {
      const auto &[a0, a1] = std::get<typename FoldStep::FS_O1>(f2.v());
      return f(a0, a1);
    } else if (std::holds_alternative<typename FoldStep::FS_O2>(f2.v())) {
      const auto &[a0, a1] = std::get<typename FoldStep::FS_O2>(f2.v());
      return f0(a0, a1);
    } else {
      const auto &[a0, a1] = std::get<typename FoldStep::FS_O4>(f2.v());
      return f1(a0, a1);
    }
  }

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, std::pair<Real, Real> &,
                                   std::pair<Real, Real> &> &&
             std::is_invocable_r_v<T1, F1 &, std::pair<Real, Real> &,
                                   std::pair<Real, Real> &> &&
             std::is_invocable_r_v<T1, F2 &, std::pair<Real, Real> &, Line &>
  static T1 FoldStep_rec(F0 &&f, F1 &&f0, F2 &&f1, const FoldStep &f2) {
    if (std::holds_alternative<typename FoldStep::FS_O1>(f2.v())) {
      const auto &[a0, a1] = std::get<typename FoldStep::FS_O1>(f2.v());
      return f(a0, a1);
    } else if (std::holds_alternative<typename FoldStep::FS_O2>(f2.v())) {
      const auto &[a0, a1] = std::get<typename FoldStep::FS_O2>(f2.v());
      return f0(a0, a1);
    } else {
      const auto &[a0, a1] = std::get<typename FoldStep::FS_O4>(f2.v());
      return f1(a0, a1);
    }
  }

  using FoldSequence = List<FoldStep>;

  struct ConstructionState {
    List<Point> state_points;
    List<Line> state_lines;

    // ACCESSORS
    ConstructionState clone() const {
      return ConstructionState{(*this).state_points.clone(),
                               (*this).state_lines.clone()};
    }
  };

  static inline const ConstructionState initial_state = ConstructionState{
      List<std::pair<Real, Real>>::cons(
          point_O, List<std::pair<Real, Real>>::cons(
                       point_X, List<std::pair<Real, Real>>::nil())),
      List<Line>::cons(line_xaxis,
                       List<Line>::cons(line_yaxis, List<Line>::nil()))};
  static ConstructionState add_fold_to_state(const ConstructionState &st,
                                             const FoldStep &step);
  static ConstructionState execute_sequence(ConstructionState st,
                                            const List<FoldStep> &seq);
  static inline const FoldSequence sample_sequence = List<FoldStep>::cons(
      FoldStep::fs_o1(point_O, point_diag),
      List<FoldStep>::cons(
          FoldStep::fs_o2(point_O, point_X),
          List<FoldStep>::cons(FoldStep::fs_o4(point_diag, line_xaxis),
                               List<FoldStep>::nil())));
  static inline const ConstructionState sample_final_state =
      execute_sequence(initial_state, sample_sequence);
  static uint64_t line_count_after_sample_sequence(const ConstructionState &st);
  static inline const uint64_t sample_sequence_length =
      sample_sequence.length();
  static inline const uint64_t sample_line_count =
      line_count_after_sample_sequence(initial_state);
  static inline const uint64_t sample_point_count =
      sample_final_state.state_points.length();
  static inline const bool sample_lines_nonempty =
      !(sample_line_count == UINT64_C(0));
  static inline const bool sample_has_expected_lines =
      sample_line_count == UINT64_C(5);
};

#endif // INCLUDED_FOLD_SEQUENCE_STATE_TRACE
