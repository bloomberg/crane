#ifndef INCLUDED_IMPLICIT_ARGS
#define INCLUDED_IMPLICIT_ARGS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct ImplicitArgs {
  template <typename T1> static T1 id(T1 x) { return x; }

  template <typename T1, typename T2> static T1 fst_of(T1 x, const T2 &) {
    return x;
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static T2 apply(F0 &&f, T1 _x0) {
    return f(_x0);
  }

  template <typename T1, typename T2 = void, typename T3, typename F0,
            typename F1>
  static T3 compose(F0 &&g, F1 &&f, const T1 &x) {
    return g(f(x));
  }

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

    mylist(mylist<A> &&_other) : v_(std::move(_other.v_)) {}

    mylist<A> &operator=(const mylist<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist<A> &operator=(mylist<A> &&_other) {
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
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, mylist<T1> &, T2 &>
  static T2 mylist_rect(T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(a0, *a1, mylist_rect<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, mylist<T1> &, T2 &>
  static T2 mylist_rec(T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(a0, *a1, mylist_rec<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1> static unsigned int length(const mylist<T1> &l) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(l.v());
      return (1u + length<T1>(*a1));
    }
  }

  static inline const unsigned int explicit_id = id<unsigned int>(5u);
  static inline const unsigned int explicit_fst =
      fst_of<unsigned int, bool>(3u, true);
  static unsigned int add_one(unsigned int _x0);
  static unsigned int double_nat(unsigned int n);
  static unsigned int add_implicit(unsigned int _x0, unsigned int _x1);
  static inline const unsigned int use_add_implicit = add_implicit(5u, 3u);
  static unsigned int scale(unsigned int _x0, unsigned int _x1);
  static inline const unsigned int use_scale = scale(3u, 7u);
  static unsigned int combine(unsigned int a, unsigned int b, unsigned int x);
  static inline const unsigned int use_combine = combine(2u, 3u, 4u);

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static unsigned int apply_implicit(F0 &&f, unsigned int _x0) {
    return f(_x0);
  }

  static inline const unsigned int use_apply_implicit = apply_implicit(
      [](unsigned int _x0) -> unsigned int { return (1u + _x0); }, 5u);
  static unsigned int with_base(unsigned int _x0, unsigned int _x1);
  static unsigned int from_zero(unsigned int _x0);
  static unsigned int from_ten(unsigned int _x0);
  static inline const unsigned int use_from_zero = from_zero(5u);
  static inline const unsigned int use_from_ten = from_ten(5u);

  template <typename T1> static T1 head_or(T1 default0, const mylist<T1> &l) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(l.v());
      return a0;
    }
  }

  static inline const unsigned int use_head_empty =
      head_or<unsigned int>(0u, mylist<unsigned int>::mynil());
  static inline const unsigned int use_head_nonempty = head_or<unsigned int>(
      0u, mylist<unsigned int>::mycons(7u, mylist<unsigned int>::mynil()));
  static unsigned int sum_with_init(unsigned int init,
                                    const mylist<unsigned int> &l);
  static inline const unsigned int use_sum_init = sum_with_init(
      5u,
      mylist<unsigned int>::mycons(
          1u, mylist<unsigned int>::mycons(2u, mylist<unsigned int>::mynil())));
  static unsigned int nested_implicits(unsigned int a, unsigned int b,
                                       unsigned int c);
  static inline const unsigned int use_nested = nested_implicits(1u, 2u, 3u);
  static unsigned int choose_branch(bool flag, unsigned int t, unsigned int f);
  static inline const unsigned int use_choose_true =
      choose_branch(true, 7u, 3u);
  static inline const unsigned int use_choose_false =
      choose_branch(false, 7u, 3u);
  static inline const unsigned int test_id = id<unsigned int>(5u);
  static inline const unsigned int test_fst =
      fst_of<unsigned int, unsigned int>(3u, 7u);
  static inline const unsigned int test_apply =
      apply<unsigned int, unsigned int>(double_nat, 5u);
  static inline const unsigned int test_compose =
      compose<unsigned int, unsigned int, unsigned int>(
          double_nat,
          [](unsigned int _x0) -> unsigned int { return (1u + _x0); }, 3u);
  static inline const unsigned int test_length =
      length<unsigned int>(mylist<unsigned int>::mycons(
          1u, mylist<unsigned int>::mycons(
                  2u, mylist<unsigned int>::mycons(
                          3u, mylist<unsigned int>::mynil()))));
  static inline const unsigned int test_explicit_id = explicit_id;
  static inline const unsigned int test_explicit_fst = explicit_fst;
  static inline const unsigned int test_add_implicit = use_add_implicit;
  static inline const unsigned int test_scale = use_scale;
  static inline const unsigned int test_combine = use_combine;
  static inline const unsigned int test_apply_implicit = use_apply_implicit;
  static inline const unsigned int test_from_zero = use_from_zero;
  static inline const unsigned int test_from_ten = use_from_ten;
  static inline const unsigned int test_head_empty = use_head_empty;
  static inline const unsigned int test_head_nonempty = use_head_nonempty;
  static inline const unsigned int test_sum_init = use_sum_init;
  static inline const unsigned int test_nested = use_nested;
  static inline const unsigned int test_choose_true = use_choose_true;
  static inline const unsigned int test_choose_false = use_choose_false;
};

#endif // INCLUDED_IMPLICIT_ARGS
