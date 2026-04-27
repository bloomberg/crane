#ifndef INCLUDED_DEEP_DESTRUCT
#define INCLUDED_DEEP_DESTRUCT

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct DeepDestruct {
  template <typename t_A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      t_A d_a0;
      std::unique_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : d_v_(_v) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    mylist(const mylist<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mylist(mylist<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    mylist<t_A> &operator=(const mylist<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    mylist<t_A> &operator=(mylist<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) mylist<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Mynil>(_sv.v())) {
        return mylist<t_A>(Mynil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Mycons>(_sv.v());
        return mylist<t_A>(Mycons{
            d_a0,
            d_a1 ? std::make_unique<DeepDestruct::mylist<t_A>>(d_a1->clone())
                 : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        d_v_ = Mynil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        d_v_ = Mycons{t_A(d_a0),
                      d_a1 ? std::make_unique<mylist<t_A>>(*d_a1) : nullptr};
      }
    }

    __attribute__((pure)) static mylist<t_A> mynil() { return mylist(Mynil{}); }

    __attribute__((pure)) static mylist<t_A> mycons(t_A a0,
                                                    const mylist<t_A> &a1) {
      return mylist(Mycons{std::move(a0), std::make_unique<mylist<t_A>>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) mylist<t_A> *operator->() { return this; }

    __attribute__((pure)) const mylist<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = mylist<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, mylist<T1>, T2> F1>
  static T2 mylist_rect(const T2 f, F1 &&f0, const mylist<T1> &m) {
    struct _Enter {
      const mylist<T1> m;
    };

    struct _Call1 {
      mylist<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{m});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const mylist<T1> m = _f.m;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<T1>::Mycons>(m.v());
          _stack.emplace_back(_Call1{*(d_a1), d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, MapsTo<T2, T1, mylist<T1>, T2> F1>
  static T2 mylist_rec(const T2 f, F1 &&f0, const mylist<T1> &m) {
    struct _Enter {
      const mylist<T1> m;
    };

    struct _Call1 {
      mylist<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{m});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const mylist<T1> m = _f.m;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<T1>::Mycons>(m.v());
          _stack.emplace_back(_Call1{*(d_a1), d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  /// Tail-recursive list builder — should compile to a loop.
  __attribute__((pure)) static mylist<unsigned int>
  build_aux(unsigned int n, mylist<unsigned int> acc);
  __attribute__((pure)) static mylist<unsigned int>
  build(const unsigned int &n);

  /// Simple accessor to observe the result.
  __attribute__((pure)) static unsigned int
  head_or_zero(const mylist<unsigned int> &l);
};

#endif // INCLUDED_DEEP_DESTRUCT
