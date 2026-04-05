#ifndef INCLUDED_FOLD_SEQUENCE_STATE_TRACE
#define INCLUDED_FOLD_SEQUENCE_STATE_TRACE

#include <crane_real.h>
#include <cstdint>
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
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

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

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons _args) -> unsigned int {
                     return (_args.d_a1->length() + 1);
                   }},
        this->v());
  }
};

struct PeanoNat {
  __attribute__((pure)) static bool eqb(const unsigned int n,
                                        const unsigned int m);
};

struct FoldSequenceStateTraceCase {
  using Point = std::pair<Real, Real>;

  struct Line {
    Real A;
    Real B;
    Real C;
  };

  struct Fold {
    // TYPES
    struct Fold_line_ctor {
      std::shared_ptr<Line> d_a0;
    };

    using variant_t = std::variant<Fold_line_ctor>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit Fold(Fold_line_ctor _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<Fold>
    fold_line_ctor(const std::shared_ptr<Line> &a0) {
      return std::make_shared<Fold>(Fold_line_ctor{a0});
    }

    static std::shared_ptr<Fold> fold_line_ctor(std::shared_ptr<Line> &&a0) {
      return std::make_shared<Fold>(Fold_line_ctor{std::move(a0)});
    }

    static std::unique_ptr<Fold>
    fold_line_ctor_uptr(const std::shared_ptr<Line> &a0) {
      return std::make_unique<Fold>(Fold_line_ctor{a0});
    }

    static std::unique_ptr<Fold>
    fold_line_ctor_uptr(std::shared_ptr<Line> &&a0) {
      return std::make_unique<Fold>(Fold_line_ctor{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    std::shared_ptr<Line> fold_line() const {
      return std::visit(
          Overloaded{[](const typename Fold::Fold_line_ctor _args)
                         -> std::shared_ptr<Line> { return _args.d_a0; }},
          this->v());
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<Line>> F0>
    T1 Fold_rec(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename Fold::Fold_line_ctor _args) -> T1 {
            return f(_args.d_a0);
          }},
          this->v());
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<Line>> F0>
    T1 Fold_rect(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename Fold::Fold_line_ctor _args) -> T1 {
            return f(_args.d_a0);
          }},
          this->v());
    }
  };

  static inline const std::shared_ptr<Line> line_xaxis = std::make_shared<Line>(
      Line{Real::from_z(INT64_C(0)), Real::from_z(INT64_C(1)),
           Real::from_z(INT64_C(0))});
  static inline const std::shared_ptr<Line> line_yaxis = std::make_shared<Line>(
      Line{Real::from_z(INT64_C(1)), Real::from_z(INT64_C(0)),
           Real::from_z(INT64_C(0))});
  static inline const Point point_O =
      std::make_pair(Real::from_z(INT64_C(0)), Real::from_z(INT64_C(0)));
  static inline const Point point_X =
      std::make_pair(Real::from_z(INT64_C(1)), Real::from_z(INT64_C(0)));
  static inline const Point point_diag =
      std::make_pair(Real::from_z(INT64_C(1)), Real::from_z(INT64_C(1)));
  static std::shared_ptr<Line> line_through(const std::pair<Real, Real> p1,
                                            const std::pair<Real, Real> p2);
  static std::shared_ptr<Line> perp_bisector(const std::pair<Real, Real> p1,
                                             const std::pair<Real, Real> p2);
  static std::shared_ptr<Line> perp_through(const std::pair<Real, Real> p,
                                            std::shared_ptr<Line> l);
  static std::shared_ptr<Fold> fold_O1(const std::pair<Real, Real> p1,
                                       const std::pair<Real, Real> p2);
  static std::shared_ptr<Fold> fold_O2(const std::pair<Real, Real> p1,
                                       const std::pair<Real, Real> p2);
  static std::shared_ptr<Fold> fold_O4(const std::pair<Real, Real> p,
                                       std::shared_ptr<Line> l);

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
      std::shared_ptr<Line> d_a1;
    };

    using variant_t = std::variant<FS_O1, FS_O2, FS_O4>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit FoldStep(FS_O1 _v) : d_v_(std::move(_v)) {}

    explicit FoldStep(FS_O2 _v) : d_v_(std::move(_v)) {}

    explicit FoldStep(FS_O4 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<FoldStep> fs_o1(Point a0, Point a1) {
      return std::make_shared<FoldStep>(FS_O1{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<FoldStep> fs_o2(Point a0, Point a1) {
      return std::make_shared<FoldStep>(FS_O2{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<FoldStep> fs_o4(Point a0,
                                           const std::shared_ptr<Line> &a1) {
      return std::make_shared<FoldStep>(FS_O4{std::move(a0), a1});
    }

    static std::shared_ptr<FoldStep> fs_o4(Point a0,
                                           std::shared_ptr<Line> &&a1) {
      return std::make_shared<FoldStep>(FS_O4{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<FoldStep> fs_o1_uptr(Point a0, Point a1) {
      return std::make_unique<FoldStep>(FS_O1{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<FoldStep> fs_o2_uptr(Point a0, Point a1) {
      return std::make_unique<FoldStep>(FS_O2{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<FoldStep>
    fs_o4_uptr(Point a0, const std::shared_ptr<Line> &a1) {
      return std::make_unique<FoldStep>(FS_O4{std::move(a0), a1});
    }

    static std::unique_ptr<FoldStep> fs_o4_uptr(Point a0,
                                                std::shared_ptr<Line> &&a1) {
      return std::make_unique<FoldStep>(FS_O4{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    std::shared_ptr<Line> execute_fold_step() const {
      return std::visit(
          Overloaded{[](const typename FoldStep::FS_O1 _args)
                         -> std::shared_ptr<Line> {
                       return fold_O1(_args.d_a0, _args.d_a1)->fold_line();
                     },
                     [](const typename FoldStep::FS_O2 _args)
                         -> std::shared_ptr<Line> {
                       return fold_O2(_args.d_a0, _args.d_a1)->fold_line();
                     },
                     [](const typename FoldStep::FS_O4 _args)
                         -> std::shared_ptr<Line> {
                       return fold_O4(_args.d_a0, _args.d_a1)->fold_line();
                     }},
          this->v());
    }
  };

  template <typename T1,
            MapsTo<T1, std::pair<Real, Real>, std::pair<Real, Real>> F0,
            MapsTo<T1, std::pair<Real, Real>, std::pair<Real, Real>> F1,
            MapsTo<T1, std::pair<Real, Real>, std::shared_ptr<Line>> F2>
  static T1 FoldStep_rect(F0 &&f, F1 &&f0, F2 &&f1,
                          const std::shared_ptr<FoldStep> &f2) {
    return std::visit(
        Overloaded{[&](const typename FoldStep::FS_O1 _args) -> T1 {
                     return f(_args.d_a0, _args.d_a1);
                   },
                   [&](const typename FoldStep::FS_O2 _args) -> T1 {
                     return f0(_args.d_a0, _args.d_a1);
                   },
                   [&](const typename FoldStep::FS_O4 _args) -> T1 {
                     return f1(_args.d_a0, _args.d_a1);
                   }},
        f2->v());
  }

  template <typename T1,
            MapsTo<T1, std::pair<Real, Real>, std::pair<Real, Real>> F0,
            MapsTo<T1, std::pair<Real, Real>, std::pair<Real, Real>> F1,
            MapsTo<T1, std::pair<Real, Real>, std::shared_ptr<Line>> F2>
  static T1 FoldStep_rec(F0 &&f, F1 &&f0, F2 &&f1,
                         const std::shared_ptr<FoldStep> &f2) {
    return std::visit(
        Overloaded{[&](const typename FoldStep::FS_O1 _args) -> T1 {
                     return f(_args.d_a0, _args.d_a1);
                   },
                   [&](const typename FoldStep::FS_O2 _args) -> T1 {
                     return f0(_args.d_a0, _args.d_a1);
                   },
                   [&](const typename FoldStep::FS_O4 _args) -> T1 {
                     return f1(_args.d_a0, _args.d_a1);
                   }},
        f2->v());
  }

  using FoldSequence = std::shared_ptr<List<std::shared_ptr<FoldStep>>>;

  struct ConstructionState {
    std::shared_ptr<List<Point>> state_points;
    std::shared_ptr<List<std::shared_ptr<Line>>> state_lines;
  };

  static inline const std::shared_ptr<ConstructionState> initial_state =
      std::make_shared<ConstructionState>(ConstructionState{
          List<std::pair<Real, Real>>::cons(
              point_O, List<std::pair<Real, Real>>::cons(
                           point_X, List<std::pair<Real, Real>>::nil())),
          List<std::shared_ptr<Line>>::cons(
              line_xaxis,
              List<std::shared_ptr<Line>>::cons(
                  line_yaxis, List<std::shared_ptr<Line>>::nil()))});
  static std::shared_ptr<ConstructionState>
  add_fold_to_state(std::shared_ptr<ConstructionState> st,
                    const std::shared_ptr<FoldStep> &step);
  static std::shared_ptr<ConstructionState>
  execute_sequence(std::shared_ptr<ConstructionState> st,
                   const std::shared_ptr<List<std::shared_ptr<FoldStep>>> &seq);
  static inline const FoldSequence sample_sequence =
      List<std::shared_ptr<FoldStep>>::cons(
          FoldStep::fs_o1(point_O, point_diag),
          List<std::shared_ptr<FoldStep>>::cons(
              FoldStep::fs_o2(point_O, point_X),
              List<std::shared_ptr<FoldStep>>::cons(
                  FoldStep::fs_o4(point_diag, line_xaxis),
                  List<std::shared_ptr<FoldStep>>::nil())));
  static inline const std::shared_ptr<ConstructionState> sample_final_state =
      execute_sequence(initial_state, sample_sequence);
  __attribute__((pure)) static unsigned int line_count_after_sample_sequence(
      const std::shared_ptr<ConstructionState> &st);
  static inline const unsigned int sample_sequence_length =
      sample_sequence->length();
  static inline const unsigned int sample_line_count =
      line_count_after_sample_sequence(initial_state);
  static inline const unsigned int sample_point_count =
      sample_final_state->state_points->length();
  static inline const bool sample_lines_nonempty =
      !(PeanoNat::eqb(sample_line_count, 0u));
  static inline const bool sample_has_expected_lines =
      PeanoNat::eqb(sample_line_count, 5u);
};

#endif // INCLUDED_FOLD_SEQUENCE_STATE_TRACE
