#ifndef INCLUDED_ROCQ_BUG_11114
#define INCLUDED_ROCQ_BUG_11114

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
  List clone() const {
    List _out{};

    struct _CloneFrame {
      const List *_src;
      List *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List *_src = _frame._src;
      List *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ =
            Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<List>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1)
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
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
  const variant_t &v() const { return d_v_; }
};

struct RocqBug11114 {
  struct t {
    // TYPES
    struct T0 {
      unsigned int d_k;
    };

    using variant_t = std::variant<T0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    t() {}

    explicit t(T0 _v) : d_v_(std::move(_v)) {}

    t(const t &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    t(t &&_other) : d_v_(std::move(_other.d_v_)) {}

    t &operator=(const t &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    t &operator=(t &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    t clone() const {
      auto &&_sv = *(this);
      const auto &[d_k] = std::get<T0>(_sv.v());
      return t(T0{d_k});
    }

    // CREATORS
    static t t0(unsigned int k) { return t(T0{std::move(k)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 t_rect(const List<unsigned int> &, F1 &&f, const t &t0) {
    const auto &[d_k] = std::get<typename t::T0>(t0.v());
    return f(d_k);
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 t_rec(const List<unsigned int> &, F1 &&f, const t &t0) {
    const auto &[d_k] = std::get<typename t::T0>(t0.v());
    return f(d_k);
  }

  struct pkg {
    List<unsigned int> _sig;
    t _t;

    // ACCESSORS
    pkg clone() const {
      return pkg{(*(this))._sig.clone(), (*(this))._t.clone()};
    }
  };

  template <MapsTo<unsigned int, unsigned int> F0>
  static pkg map(F0 &&f, const pkg &p) {
    return pkg{p._sig, [=]() mutable {
                 auto &&_sv = p._t;
                 const auto &[d_k] = std::get<typename t::T0>(_sv.v());
                 return t::t0(f(d_k));
               }()};
  }

  static inline const pkg test_pkg =
      pkg{List<unsigned int>::cons(1u, List<unsigned int>::nil()), t::t0(2u)};
  static inline const pkg test_map =
      map([](const unsigned int &x) { return (x + 1u); }, test_pkg);
};

#endif // INCLUDED_ROCQ_BUG_11114
