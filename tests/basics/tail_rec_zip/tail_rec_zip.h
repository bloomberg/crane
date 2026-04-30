#ifndef INCLUDED_TAIL_REC_ZIP
#define INCLUDED_TAIL_REC_ZIP

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A, typename t_B> struct Prod {
  // TYPES
  struct Pair {
    t_A d_a0;
    t_B d_a1;
  };

  using variant_t = std::variant<Pair>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Prod() {}

  explicit Prod(Pair _v) : d_v_(std::move(_v)) {}

  Prod(const Prod<t_A, t_B> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Prod(Prod<t_A, t_B> &&_other) : d_v_(std::move(_other.d_v_)) {}

  Prod<t_A, t_B> &operator=(const Prod<t_A, t_B> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Prod<t_A, t_B> &operator=(Prod<t_A, t_B> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Prod<t_A, t_B> clone() const {
    auto &&_sv = *(this);
    const auto &[d_a0, d_a1] = std::get<Pair>(_sv.v());
    return Prod<t_A, t_B>(Pair{d_a0, d_a1});
  }

  // CREATORS
  template <typename _U0, typename _U1>
  explicit Prod(const Prod<_U0, _U1> &_other) {
    const auto &[d_a0, d_a1] =
        std::get<typename Prod<_U0, _U1>::Pair>(_other.v());
    d_v_ = Pair{t_A(d_a0), t_B(d_a1)};
  }

  static Prod<t_A, t_B> pair(t_A a0, t_B a1) {
    return Prod(Pair{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

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

  List<t_A> rev() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<t_A>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (*(d_a1)).rev().app(List<t_A>::cons(d_a0, List<t_A>::nil()));
    }
  }

  List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(std::move(m)));
    }
  }
};

template <typename T1, typename T2>
List<Prod<T1, T2>> better_zip(const List<T1> &la, const List<T2> &lb) {
  std::function<List<Prod<T1, T2>>(List<T1>, List<T2>, List<Prod<T1, T2>>)> go;
  go = [&](List<T1> la0, List<T2> lb0,
           List<Prod<T1, T2>> acc) -> List<Prod<T1, T2>> {
    if (std::holds_alternative<typename List<T1>::Nil>(la0.v())) {
      return std::move(acc).rev();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(la0.v());
      if (std::holds_alternative<typename List<T2>::Nil>(lb0.v())) {
        return std::move(acc).rev();
      } else {
        const auto &[d_a00, d_a10] = std::get<typename List<T2>::Cons>(lb0.v());
        return go(*(d_a1), *(d_a10),
                  List<Prod<T1, T2>>::cons(Prod<T1, T2>::pair(d_a0, d_a00),
                                           std::move(acc)));
      }
    }
  };
  return go(la, lb, List<Prod<T1, T2>>::nil());
}

#endif // INCLUDED_TAIL_REC_ZIP
