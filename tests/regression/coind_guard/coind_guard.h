#ifndef INCLUDED_COIND_GUARD
#define INCLUDED_COIND_GUARD

#include "lazy.h"
#include <functional>
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

struct CoindGuard {
  template <typename t_A> struct Stream {
    // TYPES
    struct Cons {
      t_A d_a0;
      std::shared_ptr<Stream<t_A>> d_a1;
    };

    using variant_t = std::variant<Cons>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

  public:
    // CREATORS
    explicit Stream(Cons _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit Stream(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static Stream<t_A> cons(t_A a0, const Stream<t_A> &a1) {
      return Stream(Cons{std::move(a0), std::make_shared<Stream<t_A>>(a1)});
    }

    static Stream<t_A> lazy_(std::function<Stream<t_A>()> thunk) {
      return Stream<t_A>(std::function<variant_t()>([=]() mutable -> variant_t {
        Stream<t_A> _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return d_lazyV_.force(); }
  };

  template <typename T1> static T1 hd(const Stream<T1> s) {
    const auto &[d_a0, d_a1] = std::get<typename Stream<T1>::Cons>(s.v());
    return d_a0;
  }

  template <typename T1> static Stream<T1> tl(const Stream<T1> s) {
    const auto &[d_a0, d_a1] = std::get<typename Stream<T1>::Cons>(s.v());
    return Stream<T1>::lazy_([=]() mutable -> Stream<T1> { return *(d_a1); });
  }

  template <typename T1, MapsTo<T1, T1> F0>
  static Stream<T1> iterate(F0 &&f, const T1 x) {
    return Stream<T1>::lazy_([=]() mutable -> Stream<T1> {
      return Stream<T1>::cons(x, iterate<T1>(f, f(x)));
    });
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static Stream<T3> zipWith(F0 &&f, const Stream<T1> s1, const Stream<T2> s2) {
    return Stream<T3>::lazy_([=]() mutable -> Stream<T3> {
      return Stream<T3>::cons(f(hd<T1>(s1), hd<T2>(s2)),
                              zipWith<T1, T2, T3>(f, tl<T1>(s1), tl<T2>(s2)));
    });
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static Stream<T2> smap(F0 &&f, const Stream<T1> s) {
    return Stream<T2>::lazy_([=]() mutable -> Stream<T2> {
      return Stream<T2>::cons(f(hd<T1>(s)), smap<T1, T2>(f, tl<T1>(s)));
    });
  }

  template <typename T1, typename T2, MapsTo<std::pair<T1, T2>, T2> F0>
  static Stream<T1> unfold(F0 &&f, const T2 seed) {
    auto _cs = f(seed);
    const T1 &a = _cs.first;
    const T2 &s_ = _cs.second;
    return Stream<T1>::lazy_([=]() mutable -> Stream<T1> {
      return Stream<T1>::cons(a, unfold<T1, T2>(f, s_));
    });
  }

  template <typename T1>
  static List<T1> take(const unsigned int &n, const Stream<T1> s) {
    if (n <= 0) {
      return List<T1>::nil();
    } else {
      unsigned int n_ = n - 1;
      return List<T1>::cons(hd<T1>(s), take<T1>(n_, tl<T1>(s)));
    }
  }

  static inline const Stream<unsigned int> nats =
      iterate<unsigned int>([](unsigned int x) { return (x + 1); }, 0u);
  static inline const Stream<unsigned int> evens =
      smap<unsigned int, unsigned int>(
          [](const unsigned int &n) { return (n * 2u); }, nats);
  static inline const Stream<unsigned int> fibs =
      unfold<unsigned int, std::pair<unsigned int, unsigned int>>(
          [](const std::pair<unsigned int, unsigned int> &pat) {
            const unsigned int &a = pat.first;
            const unsigned int &b = pat.second;
            return std::make_pair(a, std::make_pair(b, (a + b)));
          },
          std::make_pair(0u, 1u));
  static inline const Stream<unsigned int> sum_stream =
      zipWith<unsigned int, unsigned int, unsigned int>(
          [](unsigned int _x0, unsigned int _x1) -> unsigned int {
            return (_x0 + _x1);
          },
          nats, evens);
  static inline const List<unsigned int> test_nats_5 =
      take<unsigned int>(5u, nats);
  static inline const List<unsigned int> test_evens_5 =
      take<unsigned int>(5u, evens);
  static inline const List<unsigned int> test_fibs_8 =
      take<unsigned int>(8u, fibs);
  static inline const List<unsigned int> test_sum_5 =
      take<unsigned int>(5u, sum_stream);
  static inline const unsigned int test_iterate_hd = hd<unsigned int>(nats);
};

#endif // INCLUDED_COIND_GUARD
