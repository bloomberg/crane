#ifndef INCLUDED_DEEP_APP
#define INCLUDED_DEEP_APP

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
      std::unique_ptr<mylist<A>> a1;
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

    mylist(const mylist<A> &_other) : v_(std::move(_other.clone().v_)) {}

    mylist(mylist<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    mylist<A> &operator=(const mylist<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist<A> &operator=(mylist<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    mylist<A> clone() const {
      mylist<A> _out{};

      struct _CloneFrame {
        const mylist<A> *_src;
        mylist<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist<A> *_src = _frame._src;
        mylist<A> *_dst = _frame._dst;
        if (std::holds_alternative<Mynil>(_src->v())) {
          _dst->v_ = Mynil{};
        } else {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->v_ = Mycons{_alt.a0,
                            _alt.a1 ? std::make_unique<mylist<A>>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ =
            Mycons{A(a0), a1 ? std::make_unique<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> mynil() { return mylist(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mylist<A> &_node) {
        if (std::holds_alternative<Mycons>(_node.v_)) {
          auto &_alt = std::get<Mycons>(_node.v_);
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
        _result = _f.f0(_f.a0, _f.a1, _result);
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
        _result = _f.f0(_f.a0, _f.a1, _result);
      }
    }
    return _result;
  }

  /// Tail-recursive builder — loopified.
  static mylist<unsigned int> build(unsigned int n, mylist<unsigned int> acc);

  /// Recursive app — NOT tail-recursive, so loopification won't help
  /// unless TMC kicks in.  Even with TMC, the destructor chain for
  /// the result is still deep.
  template <typename T1>
  static mylist<T1> app(const mylist<T1> &l1, mylist<T1> l2) {
    std::unique_ptr<mylist<T1>> _head{};
    std::unique_ptr<mylist<T1>> *_write = &_head;
    mylist<T1> _loop_l2 = std::move(l2);
    const mylist<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename mylist<T1>::Mynil>(_loop_l1->v())) {
        *_write = std::make_unique<mylist<T1>>(std::move(_loop_l2));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<T1>::Mycons>(_loop_l1->v());
        auto _cell = std::make_unique<mylist<T1>>(
            typename mylist<T1>::Mycons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename mylist<T1>::Mycons>((*_write)->v_mut()).a1;
        _loop_l1 = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  } /// Recursive map — same issue.

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static mylist<T2> map(F0 &&f, const mylist<T1> &l) {
    std::unique_ptr<mylist<T2>> _head{};
    std::unique_ptr<mylist<T2>> *_write = &_head;
    const mylist<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename mylist<T1>::Mynil>(_loop_l->v())) {
        *_write = std::make_unique<mylist<T2>>(mylist<T2>::mynil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<T1>::Mycons>(_loop_l->v());
        auto _cell = std::make_unique<mylist<T2>>(
            typename mylist<T2>::Mycons(f(a0), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename mylist<T2>::Mycons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }

  /// Identity map to force traversal.
  static mylist<unsigned int> map_id(const mylist<unsigned int> &l);
  /// Append two lists.
  static mylist<unsigned int> append_lists(const mylist<unsigned int> &_x0,
                                           const mylist<unsigned int> &_x1);
  static unsigned int head_or_zero(const mylist<unsigned int> &l);

  template <typename T1>
  static unsigned int
  length(const mylist<T1> &l) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const mylist<T1> *l;
    };

    /// _Resume_Mycons: resumes after recursive call with _result.
    struct _Resume_Mycons {};

    using _Frame = std::variant<_Enter, _Resume_Mycons>;
    unsigned int _result{};
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
          _result = 0u;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(l.v());
          _stack.emplace_back(_Resume_Mycons{});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Mycons>(_frame));
        _result = (_result + 1);
      }
    }
    return _result;
  }
};

#endif // INCLUDED_DEEP_APP
