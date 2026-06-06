#ifndef INCLUDED_DEEP_APP
#define INCLUDED_DEEP_APP

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct DeepApp {
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
  static T2
  mylist_rect(T2 f, F1 &&f0,
              const mylist<T1> &m) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

    struct _Enter {
      const mylist<T1> *m;
    };

    /// _Resume_Mycons: saves [f0, a1, a0], resumes after recursive call with
    /// _result.
    struct _Resume_Mycons {
      F1 f0;
      mylist<T1> a1;
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Mycons>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&m});
    /// Loopified mylist_rect: _Enter -> _Resume_Mycons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const mylist<T1> &m = *_f.m;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
          _stack.emplace_back(_Resume_Mycons{f0, *a1, a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Mycons>(_frame));
        _result = std::move(_f.f0)(std::move(_f.a0), std::move(_f.a1),
                                   std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, mylist<T1> &, T2 &>
  static T2
  mylist_rec(T2 f, F1 &&f0,
             const mylist<T1> &m) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

    struct _Enter {
      const mylist<T1> *m;
    };

    /// _Resume_Mycons: saves [f0, a1, a0], resumes after recursive call with
    /// _result.
    struct _Resume_Mycons {
      F1 f0;
      mylist<T1> a1;
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Mycons>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&m});
    /// Loopified mylist_rec: _Enter -> _Resume_Mycons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const mylist<T1> &m = *_f.m;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
          _stack.emplace_back(_Resume_Mycons{f0, *a1, a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Mycons>(_frame));
        _result = std::move(_f.f0)(std::move(_f.a0), std::move(_f.a1),
                                   std::move(_result));
      }
    }
    return _result;
  }

  /// Tail-recursive builder — loopified.
  static mylist<uint64_t> build(uint64_t n, mylist<uint64_t> acc);

  /// Recursive app — NOT tail-recursive, so loopification won't help
  /// unless TMC kicks in.  Even with TMC, the destructor chain for
  /// the result is still deep.
  template <typename T1>
  static mylist<T1> app(const mylist<T1> &l1,
                        mylist<T1> l2) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

    struct _Enter {
      mylist<T1> l2;
      const mylist<T1> *l1;
    };

    /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Mycons {
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Mycons>;
    mylist<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{std::move(l2), &l1});
    /// Loopified app: _Enter -> _Resume_Mycons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        mylist<T1> l2 = std::move(_f.l2);
        const mylist<T1> &l1 = *_f.l1;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(l1.v())) {
          _result = std::move(l2);
        } else {
          const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(l1.v());
          _stack.emplace_back(_Resume_Mycons{a0});
          _stack.emplace_back(_Enter{std::move(l2), a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Mycons>(_frame));
        _result = mylist<T1>::mycons(std::move(_f.a0), std::move(_result));
      }
    }
    return _result;
  } /// Recursive map — same issue.

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static mylist<T2>
  map(F0 &&f,
      const mylist<T1>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const mylist<T1> *l;
    };

    /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Mycons {
      T2 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Mycons>;
    mylist<T2> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified map: _Enter -> _Resume_Mycons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const mylist<T1> &l = *_f.l;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
          _result = mylist<T2>::mynil();
        } else {
          const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(l.v());
          _stack.emplace_back(_Resume_Mycons{f(a0)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Mycons>(_frame));
        _result = mylist<T2>::mycons(std::move(_f.a0), std::move(_result));
      }
    }
    return _result;
  }

  /// Identity map to force traversal.
  static mylist<uint64_t> map_id(const mylist<uint64_t> &l);
  /// Append two lists.
  static mylist<uint64_t> append_lists(const mylist<uint64_t> &_x0,
                                       const mylist<uint64_t> &_x1);
  static uint64_t head_or_zero(const mylist<uint64_t> &l);

  template <typename T1>
  static uint64_t
  length(const mylist<T1> &l) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const mylist<T1> *l;
    };

    /// _Resume_Mycons: resumes after recursive call with _result.
    struct _Resume_Mycons {};

    using _Frame = std::variant<_Enter, _Resume_Mycons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified length: _Enter -> _Resume_Mycons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const mylist<T1> &l = *_f.l;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(l.v());
          _stack.emplace_back(_Resume_Mycons{});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Mycons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

#endif // INCLUDED_DEEP_APP
