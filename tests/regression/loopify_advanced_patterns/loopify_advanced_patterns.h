#ifndef INCLUDED_LOOPIFY_ADVANCED_PATTERNS
#define INCLUDED_LOOPIFY_ADVANCED_PATTERNS

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
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
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

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
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

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct LoopifyAdvancedPatterns {
  static unsigned int len_impl(const List<unsigned int> &l);
  static List<unsigned int> as_guard(const List<unsigned int> &l);
  static unsigned int multi_guard(const List<unsigned int> &l);
  static unsigned int four_elem(const List<unsigned int> &l);
  static unsigned int nested_pattern(
      const List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>
          &l);
  static unsigned int guard_accum(unsigned int acc,
                                  const List<unsigned int> &l);
  static List<unsigned int> cons_computed(const unsigned int &n,
                                          const List<unsigned int> &l);

  struct shape {
    // TYPES
    struct Circle {
      unsigned int d_a0;
    };

    struct Square {
      unsigned int d_a0;
    };

    struct Triangle {
      unsigned int d_a0;
    };

    using variant_t = std::variant<Circle, Square, Triangle>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    shape() {}

    explicit shape(Circle _v) : d_v_(std::move(_v)) {}

    explicit shape(Square _v) : d_v_(std::move(_v)) {}

    explicit shape(Triangle _v) : d_v_(std::move(_v)) {}

    shape(const shape &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    shape(shape &&_other) : d_v_(std::move(_other.d_v_)) {}

    shape &operator=(const shape &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    shape &operator=(shape &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    shape clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Circle>(_sv.v())) {
        const auto &[d_a0] = std::get<Circle>(_sv.v());
        return shape(Circle{d_a0});
      } else if (std::holds_alternative<Square>(_sv.v())) {
        const auto &[d_a0] = std::get<Square>(_sv.v());
        return shape(Square{d_a0});
      } else {
        const auto &[d_a0] = std::get<Triangle>(_sv.v());
        return shape(Triangle{d_a0});
      }
    }

    // CREATORS
    static shape circle(unsigned int a0) {
      return shape(Circle{std::move(a0)});
    }

    static shape square(unsigned int a0) {
      return shape(Square{std::move(a0)});
    }

    static shape triangle(unsigned int a0) {
      return shape(Triangle{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2>
  static T1 shape_rect(F0 &&f, F1 &&f0, F2 &&f1, const shape &s) {
    if (std::holds_alternative<typename shape::Circle>(s.v())) {
      const auto &[d_a0] = std::get<typename shape::Circle>(s.v());
      return f(d_a0);
    } else if (std::holds_alternative<typename shape::Square>(s.v())) {
      const auto &[d_a0] = std::get<typename shape::Square>(s.v());
      return f0(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename shape::Triangle>(s.v());
      return f1(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2>
  static T1 shape_rec(F0 &&f, F1 &&f0, F2 &&f1, const shape &s) {
    if (std::holds_alternative<typename shape::Circle>(s.v())) {
      const auto &[d_a0] = std::get<typename shape::Circle>(s.v());
      return f(d_a0);
    } else if (std::holds_alternative<typename shape::Square>(s.v())) {
      const auto &[d_a0] = std::get<typename shape::Square>(s.v());
      return f0(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename shape::Triangle>(s.v());
      return f1(d_a0);
    }
  }

  static unsigned int extract_value(const shape &s);
  static unsigned int sum_shapes(const List<shape> &l);
  static std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
  count_by_shape(const List<shape> &l);
  static List<unsigned int> replace_at(const unsigned int &idx,
                                       unsigned int value,
                                       const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_ADVANCED_PATTERNS
