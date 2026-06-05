#ifndef INCLUDED_IMPLICIT_ARGS
#define INCLUDED_IMPLICIT_ARGS

#include <any>
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
      std::shared_ptr<mylist<A>> a1;
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

    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ = Mycons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
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
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? std::make_shared<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> mynil() { return mylist(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::shared_ptr<mylist<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
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

  template <typename T1> static uint64_t length(const mylist<T1> &l) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(l.v());
      return (UINT64_C(1) + length<T1>(*a1));
    }
  }

  static inline const uint64_t explicit_id = id<uint64_t>(UINT64_C(5));
  static inline const uint64_t explicit_fst =
      fst_of<uint64_t, bool>(UINT64_C(3), true);
  static uint64_t add_one(uint64_t _x0);
  static uint64_t double_nat(uint64_t n);
  static uint64_t add_implicit(uint64_t _x0, uint64_t _x1);
  static inline const uint64_t use_add_implicit =
      add_implicit(UINT64_C(5), UINT64_C(3));
  static uint64_t scale(uint64_t _x0, uint64_t _x1);
  static inline const uint64_t use_scale = scale(UINT64_C(3), UINT64_C(7));
  static uint64_t combine(uint64_t a, uint64_t b, uint64_t x);
  static inline const uint64_t use_combine =
      combine(UINT64_C(2), UINT64_C(3), UINT64_C(4));

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t apply_implicit(F0 &&f, uint64_t _x0) {
    return f(_x0);
  }

  static inline const uint64_t use_apply_implicit = apply_implicit(
      [](uint64_t _x0) -> uint64_t { return (UINT64_C(1) + _x0); },
      UINT64_C(5));
  static uint64_t with_base(uint64_t _x0, uint64_t _x1);
  static uint64_t from_zero(uint64_t _x0);
  static uint64_t from_ten(uint64_t _x0);
  static inline const uint64_t use_from_zero = from_zero(UINT64_C(5));
  static inline const uint64_t use_from_ten = from_ten(UINT64_C(5));

  template <typename T1> static T1 head_or(T1 default0, const mylist<T1> &l) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(l.v());
      return a0;
    }
  }

  static inline const uint64_t use_head_empty =
      head_or<uint64_t>(UINT64_C(0), mylist<uint64_t>::mynil());
  static inline const uint64_t use_head_nonempty = head_or<uint64_t>(
      UINT64_C(0),
      mylist<uint64_t>::mycons(UINT64_C(7), mylist<uint64_t>::mynil()));
  static uint64_t sum_with_init(uint64_t init, const mylist<uint64_t> &l);
  static inline const uint64_t use_sum_init = sum_with_init(
      UINT64_C(5),
      mylist<uint64_t>::mycons(
          UINT64_C(1),
          mylist<uint64_t>::mycons(UINT64_C(2), mylist<uint64_t>::mynil())));
  static uint64_t nested_implicits(uint64_t a, uint64_t b, uint64_t c);
  static inline const uint64_t use_nested =
      nested_implicits(UINT64_C(1), UINT64_C(2), UINT64_C(3));
  static uint64_t choose_branch(bool flag, uint64_t t, uint64_t f);
  static inline const uint64_t use_choose_true =
      choose_branch(true, UINT64_C(7), UINT64_C(3));
  static inline const uint64_t use_choose_false =
      choose_branch(false, UINT64_C(7), UINT64_C(3));
  static inline const uint64_t test_id = id<uint64_t>(UINT64_C(5));
  static inline const uint64_t test_fst =
      fst_of<uint64_t, uint64_t>(UINT64_C(3), UINT64_C(7));
  static inline const uint64_t test_apply =
      apply<uint64_t, uint64_t>(double_nat, UINT64_C(5));
  static inline const uint64_t test_compose =
      compose<uint64_t, uint64_t, uint64_t>(
          double_nat,
          [](uint64_t _x0) -> uint64_t { return (UINT64_C(1) + _x0); },
          UINT64_C(3));
  static inline const uint64_t test_length =
      length<uint64_t>(mylist<uint64_t>::mycons(
          UINT64_C(1),
          mylist<uint64_t>::mycons(
              UINT64_C(2), mylist<uint64_t>::mycons(
                               UINT64_C(3), mylist<uint64_t>::mynil()))));
  static inline const uint64_t test_explicit_id = explicit_id;
  static inline const uint64_t test_explicit_fst = explicit_fst;
  static inline const uint64_t test_add_implicit = use_add_implicit;
  static inline const uint64_t test_scale = use_scale;
  static inline const uint64_t test_combine = use_combine;
  static inline const uint64_t test_apply_implicit = use_apply_implicit;
  static inline const uint64_t test_from_zero = use_from_zero;
  static inline const uint64_t test_from_ten = use_from_ten;
  static inline const uint64_t test_head_empty = use_head_empty;
  static inline const uint64_t test_head_nonempty = use_head_nonempty;
  static inline const uint64_t test_sum_init = use_sum_init;
  static inline const uint64_t test_nested = use_nested;
  static inline const uint64_t test_choose_true = use_choose_true;
  static inline const uint64_t test_choose_false = use_choose_false;
};

#endif // INCLUDED_IMPLICIT_ARGS
