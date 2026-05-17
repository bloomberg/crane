#ifndef INCLUDED_ROCQ_BUG_13581
#define INCLUDED_ROCQ_BUG_13581

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

enum class Unit { e_TT };
enum class Bool0 { e_TRUE, e_FALSE };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::unique_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  Nat(const Nat &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Nat(Nat &&_other) : d_v_(std::move(_other.d_v_)) {}

  Nat &operator=(const Nat &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Nat &operator=(Nat &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Nat clone() const {
    Nat _out{};

    struct _CloneFrame {
      const Nat *_src;
      Nat *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Nat *_src = _frame._src;
      Nat *_dst = _frame._dst;
      if (std::holds_alternative<O>(_src->v())) {
        _dst->d_v_ = O{};
      } else {
        const auto &_alt = std::get<S>(_src->v());
        _dst->d_v_ = S{_alt.d_a0 ? std::make_unique<Nat>() : nullptr};
        auto &_dst_alt = std::get<S>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_unique<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::unique_ptr<Nat>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Nat &_node) {
      if (std::holds_alternative<S>(_node.d_v_)) {
        auto &_alt = std::get<S>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
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

  Nat add(Nat m) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return m;
    } else {
      const auto &[d_a0] = std::get<typename Nat::S>(this->v());
      return Nat::s((*d_a0).add(std::move(m)));
    }
  }
};

struct RocqBug13581 {
  template <typename t_T0> struct mixin_of {
    std::function<t_T0(t_T0)> mixin_f;

    // ACCESSORS
    mixin_of<t_T0> clone() const { return mixin_of<t_T0>{(*this).mixin_f}; }
  };

  static inline const mixin_of<Nat> d =
      mixin_of<Nat>{[](Nat x0) { return x0; }};

  template <typename t_T0> struct R {
    std::function<t_T0(t_T0)> g;
    Nat x;

    // ACCESSORS
    R<t_T0> clone() const { return R<t_T0>{(*this).g, (*this).x.clone()}; }
  };

  template <typename T1>
  static Nat y(const Nat &, const Nat &, const R<T1> &r0) {
    return r0.x.add(r0.x);
  }

  static inline const R<Nat> r = R<Nat>{[](Nat x0) { return x0; }, Nat::o()};
  template <typename t_T> struct I;
  template <typename t_T> struct J;

  template <typename t_T> struct I {
    // TYPES
    struct C {};

    struct D {
      std::unique_ptr<J<t_T>> d_a0;
    };

    using variant_t = std::variant<C, D>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    I() {}

    explicit I(C _v) : d_v_(_v) {}

    explicit I(D _v) : d_v_(std::move(_v)) {}

    I(const I<t_T> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    I(I<t_T> &&_other) : d_v_(std::move(_other.d_v_)) {}

    I<t_T> &operator=(const I<t_T> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    I<t_T> &operator=(I<t_T> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    I<t_T> clone() const {
      I<t_T> _out{};

      struct _CloneFrame {
        const I<t_T> *_src;
        I<t_T> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const I<t_T> *_src = _frame._src;
        I<t_T> *_dst = _frame._dst;
        if (std::holds_alternative<C>(_src->v())) {
          _dst->d_v_ = C{};
        } else {
          const auto &_alt = std::get<D>(_src->v());
          _dst->d_v_ = D{_alt.d_a0 ? std::make_unique<J<t_T>>() : nullptr};
          auto &_dst_alt = std::get<D>(_dst->d_v_);
          if (_alt.d_a0) {
            if (std::holds_alternative<typename RocqBug13581::J<t_T>::E>(
                    _alt.d_a0->v())) {
              const auto &_psrc =
                  std::get<typename RocqBug13581::J<t_T>::E>(_alt.d_a0->v());
              auto &_pdst = std::get<typename RocqBug13581::J<t_T>::E>(
                  _dst_alt.d_a0->v_mut());
              if (_psrc.d_a0) {
                _pdst.d_a0 = std::make_unique<I<t_T>>();
                _stack.push_back({_psrc.d_a0.get(), _pdst.d_a0.get()});
              }
            }
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit I(const I<_U> &_other) {
      if (std::holds_alternative<typename I<_U>::C>(_other.v())) {
        this->d_v_ = C{};
      } else {
        const auto &[d_a0] = std::get<typename I<_U>::D>(_other.v());
        this->d_v_ =
            D{d_a0 ? std::make_unique<RocqBug13581::J<t_T>>(*d_a0) : nullptr};
      }
    }

    static I<t_T> c() { return I(C{}); }

    static I<t_T> d(J<t_T> a0) {
      return I(D{std::make_unique<J<t_T>>(std::move(a0))});
    }

    // MANIPULATORS
    ~I() {
      std::vector<std::unique_ptr<I<t_T>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](I<t_T> &_node) {
        if (std::holds_alternative<D>(_node.d_v_)) {
          auto &_alt = std::get<D>(_node.d_v_);
          if (_alt.d_a0) {
            if (std::holds_alternative<typename RocqBug13581::J<t_T>::E>(
                    _alt.d_a0->v())) {
              auto &_palt = std::get<typename RocqBug13581::J<t_T>::E>(
                  _alt.d_a0->v_mut());
              if (_palt.d_a0) {
                _stack.push_back(std::move(_palt.d_a0));
              }
            }
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

  template <typename t_T> struct J {
    // TYPES
    struct E {
      std::unique_ptr<I<t_T>> d_a0;
    };

    using variant_t = std::variant<E>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    J() {}

    explicit J(E _v) : d_v_(std::move(_v)) {}

    J(const J<t_T> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    J(J<t_T> &&_other) : d_v_(std::move(_other.d_v_)) {}

    J<t_T> &operator=(const J<t_T> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    J<t_T> &operator=(J<t_T> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    J<t_T> clone() const {
      const auto &[d_a0] = std::get<E>(this->v());
      return J<t_T>(
          E{d_a0 ? std::make_unique<RocqBug13581::I<t_T>>(d_a0->clone())
                 : nullptr});
    }

    // CREATORS
    template <typename _U> explicit J(const J<_U> &_other) {
      const auto &[d_a0] = std::get<typename J<_U>::E>(_other.v());
      this->d_v_ =
          E{d_a0 ? std::make_unique<RocqBug13581::I<t_T>>(*d_a0) : nullptr};
    }

    static J<t_T> e(I<t_T> a0) {
      return J(E{std::make_unique<I<t_T>>(std::move(a0))});
    }

    // MANIPULATORS
    ~J() {
      std::vector<std::unique_ptr<J<t_T>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](J<t_T> &_node) {
        if (std::holds_alternative<E>(_node.d_v_)) {
          auto &_alt = std::get<E>(_node.d_v_);
          if (_alt.d_a0) {
            if (std::holds_alternative<typename RocqBug13581::I<t_T>::D>(
                    _alt.d_a0->v())) {
              auto &_palt = std::get<typename RocqBug13581::I<t_T>::D>(
                  _alt.d_a0->v_mut());
              if (_palt.d_a0) {
                _stack.push_back(std::move(_palt.d_a0));
              }
            }
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

  template <typename T1, typename T2, typename F3>
    requires std::is_invocable_r_v<T2, F3 &, J<T1> &>
  static T2 I_rect(const T1 &, const T1 &, T2 f, F3 &&f0, const Nat &,
                   const I<T1> &i) {
    if (std::holds_alternative<typename I<T1>::C>(i.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename I<T1>::D>(i.v());
      return f0(*d_a0);
    }
  }

  template <typename T1, typename T2, typename F3>
    requires std::is_invocable_r_v<T2, F3 &, J<T1> &>
  static T2 I_rec(const T1 &, const T1 &, T2 f, F3 &&f0, const Nat &,
                  const I<T1> &i) {
    if (std::holds_alternative<typename I<T1>::C>(i.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename I<T1>::D>(i.v());
      return f0(*d_a0);
    }
  }

  template <typename T1, typename T2, typename F2>
    requires std::is_invocable_r_v<T2, F2 &, I<T1> &>
  static T2 J_rect(const T1 &, const T1 &, F2 &&f, Bool0, const J<T1> &j) {
    const auto &[d_a0] = std::get<typename J<T1>::E>(j.v());
    return f(*d_a0);
  }

  template <typename T1, typename T2, typename F2>
    requires std::is_invocable_r_v<T2, F2 &, I<T1> &>
  static T2 J_rec(const T1 &, const T1 &, F2 &&f, Bool0, const J<T1> &j) {
    const auto &[d_a0] = std::get<typename J<T1>::E>(j.v());
    return f(*d_a0);
  }

  static inline const I<Nat> c = I<Nat>::d(J<Nat>::e(I<Nat>::c()));
};

#endif // INCLUDED_ROCQ_BUG_13581
