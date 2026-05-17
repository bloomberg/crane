#ifndef INCLUDED_ROCQ_BUG_13581
#define INCLUDED_ROCQ_BUG_13581

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

enum class Unit { TT };
enum class Bool0 { TRUE_, FALSE_ };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::unique_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  Nat(const Nat &_other) : v_(std::move(_other.clone().v_)) {}

  Nat(Nat &&_other) : v_(std::move(_other.v_)) {}

  Nat &operator=(const Nat &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Nat &operator=(Nat &&_other) {
    v_ = std::move(_other.v_);
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
        _dst->v_ = O{};
      } else {
        const auto &_alt = std::get<S>(_src->v());
        _dst->v_ = S{_alt.a0 ? std::make_unique<Nat>() : nullptr};
        auto &_dst_alt = std::get<S>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
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
      if (std::holds_alternative<S>(_node.v_)) {
        auto &_alt = std::get<S>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
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

  Nat add(Nat m) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return m;
    } else {
      const auto &[a0] = std::get<typename Nat::S>(this->v());
      return Nat::s((*a0).add(std::move(m)));
    }
  }
};

struct RocqBug13581 {
  template <typename T0> struct mixin_of {
    std::function<T0(T0)> mixin_f;

    // ACCESSORS
    mixin_of<T0> clone() const { return mixin_of<T0>{(*this).mixin_f}; }
  };

  static inline const mixin_of<Nat> d =
      mixin_of<Nat>{[](Nat x0) { return x0; }};

  template <typename T0> struct R {
    std::function<T0(T0)> g;
    Nat x;

    // ACCESSORS
    R<T0> clone() const { return R<T0>{(*this).g, (*this).x.clone()}; }
  };

  template <typename T1>
  static Nat y(const Nat &, const Nat &, const R<T1> &r0) {
    return r0.x.add(r0.x);
  }

  static inline const R<Nat> r = R<Nat>{[](Nat x0) { return x0; }, Nat::o()};
  template <typename T> struct I;
  template <typename T> struct J;

  template <typename T> struct I {
    // TYPES
    struct C {};

    struct D {
      std::unique_ptr<J<T>> a0;
    };

    using variant_t = std::variant<C, D>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    I() {}

    explicit I(C _v) : v_(_v) {}

    explicit I(D _v) : v_(std::move(_v)) {}

    I(const I<T> &_other) : v_(std::move(_other.clone().v_)) {}

    I(I<T> &&_other) : v_(std::move(_other.v_)) {}

    I<T> &operator=(const I<T> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    I<T> &operator=(I<T> &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    I<T> clone() const {
      I<T> _out{};

      struct _CloneFrame {
        const I<T> *_src;
        I<T> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const I<T> *_src = _frame._src;
        I<T> *_dst = _frame._dst;
        if (std::holds_alternative<C>(_src->v())) {
          _dst->v_ = C{};
        } else {
          const auto &_alt = std::get<D>(_src->v());
          _dst->v_ = D{_alt.a0 ? std::make_unique<J<T>>() : nullptr};
          auto &_dst_alt = std::get<D>(_dst->v_);
          if (_alt.a0) {
            if (std::holds_alternative<typename RocqBug13581::J<T>::E>(
                    _alt.a0->v())) {
              const auto &_psrc =
                  std::get<typename RocqBug13581::J<T>::E>(_alt.a0->v());
              auto &_pdst = std::get<typename RocqBug13581::J<T>::E>(
                  _dst_alt.a0->v_mut());
              if (_psrc.a0) {
                _pdst.a0 = std::make_unique<I<T>>();
                _stack.push_back({_psrc.a0.get(), _pdst.a0.get()});
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
        this->v_ = C{};
      } else {
        const auto &[a0] = std::get<typename I<_U>::D>(_other.v());
        this->v_ = D{a0 ? std::make_unique<RocqBug13581::J<T>>(*a0) : nullptr};
      }
    }

    static I<T> c() { return I(C{}); }

    static I<T> d(J<T> a0) {
      return I(D{std::make_unique<J<T>>(std::move(a0))});
    }

    // MANIPULATORS
    ~I() {
      std::vector<std::unique_ptr<I<T>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](I<T> &_node) {
        if (std::holds_alternative<D>(_node.v_)) {
          auto &_alt = std::get<D>(_node.v_);
          if (_alt.a0) {
            if (std::holds_alternative<typename RocqBug13581::J<T>::E>(
                    _alt.a0->v())) {
              auto &_palt =
                  std::get<typename RocqBug13581::J<T>::E>(_alt.a0->v_mut());
              if (_palt.a0) {
                _stack.push_back(std::move(_palt.a0));
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

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T> struct J {
    // TYPES
    struct E {
      std::unique_ptr<I<T>> a0;
    };

    using variant_t = std::variant<E>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    J() {}

    explicit J(E _v) : v_(std::move(_v)) {}

    J(const J<T> &_other) : v_(std::move(_other.clone().v_)) {}

    J(J<T> &&_other) : v_(std::move(_other.v_)) {}

    J<T> &operator=(const J<T> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    J<T> &operator=(J<T> &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    J<T> clone() const {
      const auto &[a0] = std::get<E>(this->v());
      return J<T>(
          E{a0 ? std::make_unique<RocqBug13581::I<T>>(a0->clone()) : nullptr});
    }

    // CREATORS
    template <typename _U> explicit J(const J<_U> &_other) {
      const auto &[a0] = std::get<typename J<_U>::E>(_other.v());
      this->v_ = E{a0 ? std::make_unique<RocqBug13581::I<T>>(*a0) : nullptr};
    }

    static J<T> e(I<T> a0) {
      return J(E{std::make_unique<I<T>>(std::move(a0))});
    }

    // MANIPULATORS
    ~J() {
      std::vector<std::unique_ptr<J<T>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](J<T> &_node) {
        if (std::holds_alternative<E>(_node.v_)) {
          auto &_alt = std::get<E>(_node.v_);
          if (_alt.a0) {
            if (std::holds_alternative<typename RocqBug13581::I<T>::D>(
                    _alt.a0->v())) {
              auto &_palt =
                  std::get<typename RocqBug13581::I<T>::D>(_alt.a0->v_mut());
              if (_palt.a0) {
                _stack.push_back(std::move(_palt.a0));
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

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F3>
    requires std::is_invocable_r_v<T2, F3 &, J<T1> &>
  static T2 I_rect(const T1 &, const T1 &, T2 f, F3 &&f0, const Nat &,
                   const I<T1> &i) {
    if (std::holds_alternative<typename I<T1>::C>(i.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename I<T1>::D>(i.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename T2, typename F3>
    requires std::is_invocable_r_v<T2, F3 &, J<T1> &>
  static T2 I_rec(const T1 &, const T1 &, T2 f, F3 &&f0, const Nat &,
                  const I<T1> &i) {
    if (std::holds_alternative<typename I<T1>::C>(i.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename I<T1>::D>(i.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename T2, typename F2>
    requires std::is_invocable_r_v<T2, F2 &, I<T1> &>
  static T2 J_rect(const T1 &, const T1 &, F2 &&f, Bool0, const J<T1> &j) {
    const auto &[a0] = std::get<typename J<T1>::E>(j.v());
    return f(*a0);
  }

  template <typename T1, typename T2, typename F2>
    requires std::is_invocable_r_v<T2, F2 &, I<T1> &>
  static T2 J_rec(const T1 &, const T1 &, F2 &&f, Bool0, const J<T1> &j) {
    const auto &[a0] = std::get<typename J<T1>::E>(j.v());
    return f(*a0);
  }

  static inline const I<Nat> c = I<Nat>::d(J<Nat>::e(I<Nat>::c()));
};

#endif // INCLUDED_ROCQ_BUG_13581
