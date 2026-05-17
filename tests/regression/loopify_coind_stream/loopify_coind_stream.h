#ifndef INCLUDED_LOOPIFY_COIND_STREAM
#define INCLUDED_LOOPIFY_COIND_STREAM

#include "lazy.h"
#include <functional>
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

struct LoopifyCoindStream {
  template <typename A> struct stream {
    // TYPES
    struct Scons {
      A a0;
      std::shared_ptr<stream<A>> a1;
    };

    using variant_t = std::variant<Scons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    explicit stream(Scons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream<A> scons(A a0, const stream<A> &a1) {
      return stream(Scons{std::move(a0), std::make_shared<stream<A>>(a1)});
    }

    static stream<A> lazy_(std::function<stream<A>()> thunk) {
      return stream<A>(std::function<variant_t()>([=]() mutable -> variant_t {
        stream<A> _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }
  };

  template <typename T1> static T1 hd(stream<T1> s) {
    const auto &[a0, a1] = std::get<typename stream<T1>::Scons>(s.v());
    return a0;
  }

  template <typename T1> static stream<T1> tl(stream<T1> s) {
    const auto &[a0, a1] = std::get<typename stream<T1>::Scons>(s.v());
    return stream<T1>::lazy_([=]() mutable -> stream<T1> { return *a1; });
  }

  template <typename T1> static List<T1> take(uint64_t n, stream<T1> s) {
    std::unique_ptr<List<T1>> _head{};
    std::unique_ptr<List<T1>> *_write = &_head;
    stream<T1> _loop_s = std::move(s);
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        *_write = std::make_unique<List<T1>>(List<T1>::nil());
        break;
      } else {
        uint64_t n_ = _loop_n - 1;
        auto _cell = std::make_unique<List<T1>>(
            typename List<T1>::Cons(hd<T1>(_loop_s), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).a1;
        _loop_s = tl<T1>(_loop_s);
        _loop_n = n_;
        continue;
      }
    }
    return std::move(*_head);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &>
  static stream<T1> iterate(F0 &&f, T1 x) {
    return stream<T1>::lazy_([=]() mutable -> stream<T1> {
      return stream<T1>::scons(x, iterate<T1>(f, f(x)));
    });
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static stream<T2> smap(F0 &&f, stream<T1> s) {
    return stream<T2>::lazy_([=]() mutable -> stream<T2> {
      return stream<T2>::scons(f(hd<T1>(s)), smap<T1, T2>(f, tl<T1>(s)));
    });
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static stream<T3> zipWith(F0 &&f, stream<T1> s1, stream<T2> s2) {
    return stream<T3>::lazy_([=]() mutable -> stream<T3> {
      return stream<T3>::scons(f(hd<T1>(s1), hd<T2>(s2)),
                               zipWith<T1, T2, T3>(f, tl<T1>(s1), tl<T2>(s2)));
    });
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<std::pair<T1, T2>, F0 &, T2 &>
  static stream<T1> unfold(F0 &&f, const T2 &seed) {
    auto _cs = f(seed);
    const T1 &a = _cs.first;
    const T2 &s_ = _cs.second;
    return stream<T1>::lazy_([=]() mutable -> stream<T1> {
      return stream<T1>::scons(a, unfold<T1, T2>(f, s_));
    });
  }

  static inline const stream<uint64_t> nats =
      iterate<uint64_t>([](uint64_t x) { return (x + 1); }, UINT64_C(0));
  static inline const stream<uint64_t> doubled = smap<uint64_t, uint64_t>(
      [](uint64_t n) { return (n * UINT64_C(2)); }, nats);
  static inline const stream<uint64_t> sum_stream =
      zipWith<uint64_t, uint64_t, uint64_t>(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
          nats, doubled);
  static inline const stream<uint64_t> fibs =
      unfold<uint64_t, std::pair<uint64_t, uint64_t>>(
          [](const std::pair<uint64_t, uint64_t> &pat) {
            const uint64_t &a = pat.first;
            const uint64_t &b = pat.second;
            return std::make_pair(a, std::make_pair(b, (a + b)));
          },
          std::make_pair(UINT64_C(0), UINT64_C(1)));
  static inline const List<uint64_t> test_nats_5 =
      take<uint64_t>(UINT64_C(5), nats);
  static inline const List<uint64_t> test_doubled_5 =
      take<uint64_t>(UINT64_C(5), doubled);
  static inline const List<uint64_t> test_sum_5 =
      take<uint64_t>(UINT64_C(5), sum_stream);
  static inline const List<uint64_t> test_fibs_8 =
      take<uint64_t>(UINT64_C(8), fibs);
};

#endif // INCLUDED_LOOPIFY_COIND_STREAM
