#ifndef INCLUDED_DEEP_APP
#define INCLUDED_DEEP_APP

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct DeepApp {
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
            d_a0, d_a1 ? std::make_unique<DeepApp::mylist<t_A>>(d_a1->clone())
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

    __attribute__((pure)) static mylist<t_A> mycons(t_A a0, mylist<t_A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist<t_A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist>> _stack;
      auto _drain = [&](mylist &_node) {
        if (std::holds_alternative<Mycons>(_node.d_v_)) {
          auto &_alt = std::get<Mycons>(_node.d_v_);
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
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, mylist<T1>, T2> F1>
  static T2 mylist_rect(const T2 f, F1 &&f0, const mylist<T1> &m) {
    struct _Enter {
      const mylist<T1> *m;
    };

    struct _Call1 {
      mylist<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{&m});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const mylist<T1> &m = *(_f.m);
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<T1>::Mycons>(m.v());
          _stack.emplace_back(_Call1{*(d_a1), d_a0});
          _stack.emplace_back(_Enter{d_a1.get()});
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
      const mylist<T1> *m;
    };

    struct _Call1 {
      mylist<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{&m});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const mylist<T1> &m = *(_f.m);
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<T1>::Mycons>(m.v());
          _stack.emplace_back(_Call1{*(d_a1), d_a0});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  /// Tail-recursive builder — loopified.
  __attribute__((pure)) static mylist<unsigned int>
  build(unsigned int n, mylist<unsigned int> acc);

  /// Recursive app — NOT tail-recursive, so loopification won't help
  /// unless TMC kicks in.  Even with TMC, the destructor chain for
  /// the result is still deep.
  template <typename T1>
  __attribute__((pure)) static mylist<T1> app(const mylist<T1> &l1,
                                              mylist<T1> l2) {
    std::unique_ptr<mylist<T1>> _head{};
    std::unique_ptr<mylist<T1>> *_write = &_head;
    mylist<T1> _loop_l2 = std::move(l2);
    const mylist<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename mylist<T1>::Mynil>(_loop_l1->v())) {
        *(_write) = std::make_unique<mylist<T1>>(std::move(_loop_l2));
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<T1>::Mycons>(_loop_l1->v());
        auto _cell = std::make_unique<mylist<T1>>(
            typename mylist<T1>::Mycons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename mylist<T1>::Mycons>((*_write)->v_mut()).d_a1;
        mylist<T1> _next_l2 = std::move(_loop_l2);
        const mylist<T1> *_next_l1 = d_a1.get();
        _loop_l2 = std::move(_next_l2);
        _loop_l1 = _next_l1;
        continue;
      }
    }
    return std::move(*(_head));
  } /// Recursive map — same issue.

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static mylist<T2> map(F0 &&f, const mylist<T1> &l) {
    std::unique_ptr<mylist<T2>> _head{};
    std::unique_ptr<mylist<T2>> *_write = &_head;
    const mylist<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename mylist<T1>::Mynil>(_loop_l->v())) {
        *(_write) = std::make_unique<mylist<T2>>(mylist<T2>::mynil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<T1>::Mycons>(_loop_l->v());
        auto _cell = std::make_unique<mylist<T2>>(
            typename mylist<T2>::Mycons(f(d_a0), nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename mylist<T2>::Mycons>((*_write)->v_mut()).d_a1;
        _loop_l = d_a1.get();
        continue;
      }
    }
    return std::move(*(_head));
  }

  /// Identity map to force traversal.
  __attribute__((pure)) static mylist<unsigned int>
  map_id(const mylist<unsigned int> &l);
  /// Append two lists.
  __attribute__((pure)) static mylist<unsigned int>
  append_lists(const mylist<unsigned int> &_x0,
               const mylist<unsigned int> &_x1);
  __attribute__((pure)) static unsigned int
  head_or_zero(const mylist<unsigned int> &l);

  template <typename T1>
  __attribute__((pure)) static unsigned int length(const mylist<T1> &l) {
    struct _Enter {
      const mylist<T1> *l;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{&l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const mylist<T1> &l = *(_f.l);
        if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<T1>::Mycons>(l.v());
          _stack.emplace_back(_Call1{});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = (_result + 1);
      }
    }
    return _result;
  }
};

#endif // INCLUDED_DEEP_APP
