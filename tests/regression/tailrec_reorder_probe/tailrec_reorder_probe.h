#ifndef INCLUDED_TAILREC_REORDER_PROBE
#define INCLUDED_TAILREC_REORDER_PROBE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct TailrecReorderProbe {
  /// Custom list to control exact code generation.
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

  /// Tail-recursive reverse via accumulator.
  ///
  /// BUG HYPOTHESIS: When loopified, the assignments to loop variables
  /// l := t and acc := mycons h acc must happen in the right order.
  /// If l := t fires first, the old list node may be freed (when
  /// use_count drops to 0), making h a dangling reference in the
  /// subsequent mycons h acc construction.
  ///
  /// This is a potential evaluation-order / use-after-free bug in the
  /// loopify pass.
  template <typename T1>
  static mylist<T1> my_rev_append(const mylist<T1> &l, mylist<T1> acc) {
    mylist<T1> _loop_acc = std::move(acc);
    const mylist<T1> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename mylist<T1>::Mynil>(_loop_l->v())) {
        return _loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<T1>::Mycons>(_loop_l->v());
        _loop_acc = mylist<T1>::mycons(a0, std::move(_loop_acc));
        _loop_l = a1.get();
      }
    }
  }

  template <typename T1> static mylist<T1> my_reverse(const mylist<T1> &l) {
    return my_rev_append<T1>(l, mylist<T1>::mynil());
  }

  /// Variant: TWO arguments depend on pattern-matched fields.
  /// l := t, acc1 := mycons h acc1, acc2 := mycons (h+1) acc2
  /// Both acc1 and acc2 need h from the OLD l.
  static std::pair<mylist<uint64_t>, mylist<uint64_t>>
  dual_accum(const mylist<uint64_t> &l, mylist<uint64_t> acc1,
             mylist<uint64_t> acc2);

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, T1 &>
  static uint64_t
  mylist_sum(F0 &&f,
             const mylist<T1> &l) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

    struct _Enter {
      const mylist<T1> *l;
    };

    /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Mycons {
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Mycons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified mylist_sum: _Enter -> _Resume_Mycons.
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
          _stack.emplace_back(_Resume_Mycons{f(a0)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Mycons>(_frame));
        _result = (_f.a0 + _result);
      }
    }
    return _result;
  }

  static inline const uint64_t test_rev = mylist_sum<uint64_t>(
      [](uint64_t x) { return x; },
      my_reverse<uint64_t>(mylist<uint64_t>::mycons(
          UINT64_C(1),
          mylist<uint64_t>::mycons(
              UINT64_C(2), mylist<uint64_t>::mycons(
                               UINT64_C(3), mylist<uint64_t>::mynil())))));
  static inline const uint64_t test_dual = []() -> uint64_t {
    auto _cs = dual_accum(
        mylist<uint64_t>::mycons(
            UINT64_C(10),
            mylist<uint64_t>::mycons(
                UINT64_C(20), mylist<uint64_t>::mycons(
                                  UINT64_C(30), mylist<uint64_t>::mynil()))),
        mylist<uint64_t>::mynil(), mylist<uint64_t>::mynil());
    const mylist<uint64_t> &a = _cs.first;
    const mylist<uint64_t> &b = _cs.second;
    return (mylist_sum<uint64_t>([](uint64_t x) { return x; }, a) +
            mylist_sum<uint64_t>([](uint64_t x) { return x; }, b));
  }();
  /// Tail-recursive function where the recursive argument is a COMPLEX
  /// expression involving multiple pattern variables.
  static mylist<uint64_t> weave(const mylist<uint64_t> &l1,
                                const mylist<uint64_t> &l2,
                                mylist<uint64_t> acc);
  static inline const uint64_t test_weave = mylist_sum<uint64_t>(
      [](uint64_t x) { return x; },
      weave(mylist<uint64_t>::mycons(
                UINT64_C(1), mylist<uint64_t>::mycons(
                                 UINT64_C(3), mylist<uint64_t>::mynil())),
            mylist<uint64_t>::mycons(
                UINT64_C(2), mylist<uint64_t>::mycons(
                                 UINT64_C(4), mylist<uint64_t>::mynil())),
            mylist<uint64_t>::mynil()));
};

#endif // INCLUDED_TAILREC_REORDER_PROBE
