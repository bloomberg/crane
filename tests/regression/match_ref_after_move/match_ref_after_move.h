#ifndef INCLUDED_MATCH_REF_AFTER_MOVE
#define INCLUDED_MATCH_REF_AFTER_MOVE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MatchRefAfterMove {
  /// This test exercises patterns where a value is destructured
  /// and then the original is also used, testing move/reference
  /// interactions in the generated C++.
  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::unique_ptr<mylist<A>> a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : v_(_v) {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    mylist(const mylist<A> &_other) : v_(std::move(_other.clone().v_)) {}

    mylist(mylist<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    mylist<A> &operator=(const mylist<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist<A> &operator=(mylist<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    mylist<A> clone() const {
      mylist<A> _out{};

      struct _CloneFrame {
        const mylist<A> *_src;
        mylist<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist<A> *_src = _frame._src;
        mylist<A> *_dst = _frame._dst;
        if (std::holds_alternative<Mynil>(_src->v())) {
          _dst->v_ = Mynil{};
        } else {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->v_ = Mycons{_alt.a0,
                            _alt.a1 ? std::make_unique<mylist<A>>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ =
            Mycons{A(a0), a1 ? std::make_unique<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> mynil() { return mylist(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mylist<A> &_node) {
        if (std::holds_alternative<Mycons>(_node.v_)) {
          auto &_alt = std::get<Mycons>(_node.v_);
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

    /// Pattern 1: Match on a list, return head AND apply a function
    /// to the tail that also takes the head as argument.
    /// The generated code must ensure h survives until both uses.
    uint64_t mylist_length() const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return (UINT64_C(1) + a1->mylist_length());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return f0(a0, *a1, a1->template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return f0(a0, *a1, a1->template mylist_rect<T1>(f, f0));
      }
    }
  };

  template <typename A, typename B> struct mypair {
    // DATA
    A a0;
    B a1;

    // ACCESSORS
    mypair<A, B> clone() const { return {a0, a1}; }

    // CREATORS
    static mypair<A, B> mkpair(A a0, B a1) {
      return {std::move(a0), std::move(a1)};
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 mypair_rec(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0, a1] = _sv;
      return f(a0, a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 mypair_rect(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0, a1] = _sv;
      return f(a0, a1);
    }
  };

  static mypair<uint64_t, uint64_t>
  head_and_tail_length(const mylist<uint64_t> &l);
  /// Pattern 2: Nested match where inner match is on a field of outer.
  /// After inner match, outer pattern variables are still used.
  ///
  /// BUG HYPOTHESIS: Outer match creates structured bindings into the
  /// outer value. Inner match on the tail might consume/move the tail.
  /// If the outer head h is a reference into the outer value, and
  /// the outer value is freed because the inner match consumes the
  /// tail (sole remaining reference), h dangles.
  static uint64_t nested_match_probe(const mylist<uint64_t> &l);
  /// Pattern 3: Build a pair where one element is from a match
  /// and the other is a function of the matched value.
  /// Tests evaluation order in pair construction.
  static mypair<uint64_t, mylist<uint64_t>>
  match_into_pair(const mylist<uint64_t> &l);
  /// Pattern 4: Double match on same value.
  /// First match extracts head, second match extracts tail.
  /// Between matches, the value might be moved.
  static mypair<uint64_t, mylist<uint64_t>>
  double_match(const mylist<uint64_t> &l);
  static uint64_t mylist_sum(const mylist<uint64_t> &l);
  /// test1: head_and_tail_length 10,20,30 = (10, 2)
  static inline const uint64_t test1 = []() {
    const auto &_sv0 = head_and_tail_length(mylist<uint64_t>::mycons(
        UINT64_C(10),
        mylist<uint64_t>::mycons(
            UINT64_C(20), mylist<uint64_t>::mycons(
                              UINT64_C(30), mylist<uint64_t>::mynil()))));
    const auto &[a00, a10] = _sv0;
    return (a00 + a10);
  }();
  /// test2: nested_match_probe 10,20,30 = 10+20+1 = 31
  static inline const uint64_t test2 =
      nested_match_probe(mylist<uint64_t>::mycons(
          UINT64_C(10),
          mylist<uint64_t>::mycons(
              UINT64_C(20), mylist<uint64_t>::mycons(
                                UINT64_C(30), mylist<uint64_t>::mynil()))));
  /// test3: match_into_pair 5,10 = (5, 6,10)
  static inline const uint64_t test3 = []() {
    const auto &_sv1 = match_into_pair(mylist<uint64_t>::mycons(
        UINT64_C(5),
        mylist<uint64_t>::mycons(UINT64_C(10), mylist<uint64_t>::mynil())));
    const auto &[a01, a11] = _sv1;
    return (a01 + mylist_sum(a11));
  }();
  /// test4: double_match 7,8,9 = (7, 8,9)
  static inline const uint64_t test4 = []() {
    const auto &_sv2 = double_match(mylist<uint64_t>::mycons(
        UINT64_C(7),
        mylist<uint64_t>::mycons(
            UINT64_C(8),
            mylist<uint64_t>::mycons(UINT64_C(9), mylist<uint64_t>::mynil()))));
    const auto &[a02, a12] = _sv2;
    return (a02 + mylist_sum(a12));
  }();

  /// Pattern 5: CPS with explicit continuation that captures from match.
  /// The continuation is a SIMPLE lambda, not a fixpoint.
  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &, uint64_t &>
  static uint64_t match_with_cont(const mylist<uint64_t> &l, F1 &&k) {
    if (std::holds_alternative<typename mylist<uint64_t>::Mynil>(l.v())) {
      return k(UINT64_C(0), UINT64_C(0));
    } else {
      const auto &[a0, a1] = std::get<typename mylist<uint64_t>::Mycons>(l.v());
      return k(a0, a1->mylist_length());
    }
  }

  /// test5: match_with_cont 100, 200, 300 (+) = 100 + 2 = 102
  static inline const uint64_t test5 = match_with_cont(
      mylist<uint64_t>::mycons(
          UINT64_C(100),
          mylist<uint64_t>::mycons(
              UINT64_C(200), mylist<uint64_t>::mycons(
                                 UINT64_C(300), mylist<uint64_t>::mynil()))),
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); });

  /// Pattern 6: Deep nesting of matches with multiple constructors.
  template <typename A, typename B> struct either {
    // TYPES
    struct Left {
      A a0;
    };

    struct Right {
      B a0;
    };

    using variant_t = std::variant<Left, Right>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    either() {}

    explicit either(Left _v) : v_(std::move(_v)) {}

    explicit either(Right _v) : v_(std::move(_v)) {}

    either(const either<A, B> &_other) : v_(_other.v_) {}

    either(either<A, B> &&_other) noexcept : v_(std::move(_other.v_)) {}

    either<A, B> &operator=(const either<A, B> &_other) {
      v_ = _other.v_;
      return *this;
    }

    either<A, B> &operator=(either<A, B> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    either<A, B> clone() const {
      if (std::holds_alternative<Left>(this->v())) {
        const auto &[a0] = std::get<Left>(this->v());
        return either<A, B>(Left{a0});
      } else {
        const auto &[a0] = std::get<Right>(this->v());
        return either<A, B>(Right{a0});
      }
    }

    // CREATORS
    template <typename _U0, typename _U1>
    explicit either(const either<_U0, _U1> &_other) {
      if (std::holds_alternative<typename either<_U0, _U1>::Left>(_other.v())) {
        const auto &[a0] =
            std::get<typename either<_U0, _U1>::Left>(_other.v());
        this->v_ = Left{A(a0)};
      } else {
        const auto &[a0] =
            std::get<typename either<_U0, _U1>::Right>(_other.v());
        this->v_ = Right{B(a0)};
      }
    }

    static either<A, B> left(A a0) { return either(Left{std::move(a0)}); }

    static either<A, B> right(B a0) { return either(Right{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, A &> &&
               std::is_invocable_r_v<T1, F1 &, B &>
    T1 either_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename either<A, B>::Left>(this->v())) {
        const auto &[a0] = std::get<typename either<A, B>::Left>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename either<A, B>::Right>(this->v());
        return f0(a0);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, A &> &&
               std::is_invocable_r_v<T1, F1 &, B &>
    T1 either_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename either<A, B>::Left>(this->v())) {
        const auto &[a0] = std::get<typename either<A, B>::Left>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename either<A, B>::Right>(this->v());
        return f0(a0);
      }
    }
  };

  static uint64_t
  complex_match(const either<mylist<uint64_t>, mylist<uint64_t>> &e);
  /// test6: complex_match (Right 50, 60) = 50 + 1 = 51
  static inline const uint64_t test6 =
      complex_match(either<mylist<uint64_t>, mylist<uint64_t>>::right(
          mylist<uint64_t>::mycons(
              UINT64_C(50), mylist<uint64_t>::mycons(
                                UINT64_C(60), mylist<uint64_t>::mynil()))));
};

#endif // INCLUDED_MATCH_REF_AFTER_MOVE
