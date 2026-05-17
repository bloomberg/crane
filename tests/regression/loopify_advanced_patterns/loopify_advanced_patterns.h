#ifndef INCLUDED_LOOPIFY_ADVANCED_PATTERNS
#define INCLUDED_LOOPIFY_ADVANCED_PATTERNS

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
  static List<unsigned int> cons_computed(unsigned int n,
                                          const List<unsigned int> &l);

  struct shape {
    // TYPES
    struct Circle {
      unsigned int a0;
    };

    struct Square {
      unsigned int a0;
    };

    struct Triangle {
      unsigned int a0;
    };

    using variant_t = std::variant<Circle, Square, Triangle>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    shape() {}

    explicit shape(Circle _v) : v_(std::move(_v)) {}

    explicit shape(Square _v) : v_(std::move(_v)) {}

    explicit shape(Triangle _v) : v_(std::move(_v)) {}

    shape(const shape &_other) : v_(std::move(_other.clone().v_)) {}

    shape(shape &&_other) noexcept : v_(std::move(_other.v_)) {}

    shape &operator=(const shape &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    shape &operator=(shape &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    shape clone() const {
      if (std::holds_alternative<Circle>(this->v())) {
        const auto &[a0] = std::get<Circle>(this->v());
        return shape(Circle{a0});
      } else if (std::holds_alternative<Square>(this->v())) {
        const auto &[a0] = std::get<Square>(this->v());
        return shape(Square{a0});
      } else {
        const auto &[a0] = std::get<Triangle>(this->v());
        return shape(Triangle{a0});
      }
    }

    // CREATORS
    static shape circle(unsigned int a0) { return shape(Circle{a0}); }

    static shape square(unsigned int a0) { return shape(Square{a0}); }

    static shape triangle(unsigned int a0) { return shape(Triangle{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F2 &, unsigned int &>
  static T1 shape_rect(F0 &&f, F1 &&f0, F2 &&f1, const shape &s) {
    if (std::holds_alternative<typename shape::Circle>(s.v())) {
      const auto &[a0] = std::get<typename shape::Circle>(s.v());
      return f(a0);
    } else if (std::holds_alternative<typename shape::Square>(s.v())) {
      const auto &[a0] = std::get<typename shape::Square>(s.v());
      return f0(a0);
    } else {
      const auto &[a0] = std::get<typename shape::Triangle>(s.v());
      return f1(a0);
    }
  }

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F2 &, unsigned int &>
  static T1 shape_rec(F0 &&f, F1 &&f0, F2 &&f1, const shape &s) {
    if (std::holds_alternative<typename shape::Circle>(s.v())) {
      const auto &[a0] = std::get<typename shape::Circle>(s.v());
      return f(a0);
    } else if (std::holds_alternative<typename shape::Square>(s.v())) {
      const auto &[a0] = std::get<typename shape::Square>(s.v());
      return f0(a0);
    } else {
      const auto &[a0] = std::get<typename shape::Triangle>(s.v());
      return f1(a0);
    }
  }

  static unsigned int extract_value(const shape &s);
  static unsigned int sum_shapes(const List<shape> &l);
  static std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
  count_by_shape(const List<shape> &l);
  static List<unsigned int> replace_at(unsigned int idx, unsigned int value,
                                       const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_ADVANCED_PATTERNS
