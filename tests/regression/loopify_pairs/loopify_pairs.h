#ifndef INCLUDED_LOOPIFY_PAIRS
#define INCLUDED_LOOPIFY_PAIRS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Consolidated UNIQUE pair/tuple operations.
struct LoopifyPairs {
  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::unique_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : d_v_(_v) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    list(const list<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    list(list<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    list<t_A> &operator=(const list<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    list<t_A> &operator=(list<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    list<t_A> clone() const {
      list<t_A> _out{};

      struct _CloneFrame {
        const list<t_A> *_src;
        list<t_A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const list<t_A> *_src = _frame._src;
        list<t_A> *_dst = _frame._dst;
        if (std::holds_alternative<Nil>(_src->v())) {
          _dst->d_v_ = Nil{};
        } else {
          const auto &_alt = std::get<Cons>(_src->v());
          _dst->d_v_ = Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<list<t_A>>()
                                                 : nullptr};
          auto &_dst_alt = std::get<Cons>(_dst->d_v_);
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        this->d_v_ = Nil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<_U>::Cons>(_other.v());
        this->d_v_ = Cons{t_A(d_a0),
                          d_a1 ? std::make_unique<list<t_A>>(*d_a1) : nullptr};
      }
    }

    static list<t_A> nil() { return list(Nil{}); }

    static list<t_A> cons(t_A a0, list<t_A> a1) {
      return list(
          Cons{std::move(a0), std::make_unique<list<t_A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      std::vector<std::unique_ptr<list<t_A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](list<t_A> &_node) {
        if (std::holds_alternative<Cons>(_node.d_v_)) {
          auto &_alt = std::get<Cons>(_node.d_v_);
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
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

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2
  list_rect(T2 f, F1 &&f0,
            const list<T1> &l) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [f0, d_a1, d_a0], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      F1 f0;
      list<T1> d_a1;
      T1 d_a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified list_rect: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *(_f.l);
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f0, *(d_a1), d_a0});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.f0(_f.d_a0, _f.d_a1, _result);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2
  list_rec(T2 f, F1 &&f0,
           const list<T1> &l) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [f0, d_a1, d_a0], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      F1 f0;
      list<T1> d_a1;
      T1 d_a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified list_rec: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *(_f.l);
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f0, *(d_a1), d_a0});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.f0(_f.d_a0, _f.d_a1, _result);
      }
    }
    return _result;
  }

  /// partition p l splits into (satisfies p, doesn't satisfy p).
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static std::pair<list<T1>, list<T1>>
  partition(F0 &&p,
            const list<T1> &l) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Cont_Cons: saves [d_a0, p], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Cons {
      T1 d_a0;
      F0 p;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    std::pair<list<T1>, list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified partition: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *(_f.l);
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{d_a0, p});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        T1 d_a0 = _f.d_a0;
        F0 p = _f.p;
        const list<T1> &yes = _result.first;
        const list<T1> &no = _result.second;
        if (p(d_a0)) {
          _result = std::make_pair(list<T1>::cons(d_a0, yes), no);
        } else {
          _result = std::make_pair(yes, list<T1>::cons(d_a0, no));
        }
      }
    }
    return _result;
  }

  /// unzip l splits list of nat pairs into pair of lists.
  static std::pair<list<unsigned int>, list<unsigned int>>
  unzip(const list<std::pair<unsigned int, unsigned int>> &l);

  /// zip combines two lists into pairs.
  template <typename T1, typename T2>
  static list<std::pair<T1, T2>> zip(const list<T1> &l1, const list<T2> &l2) {
    std::unique_ptr<list<std::pair<T1, T2>>> _head{};
    std::unique_ptr<list<std::pair<T1, T2>>> *_write = &_head;
    const list<T2> *_loop_l2 = &l2;
    const list<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1->v())) {
        *(_write) = std::make_unique<list<std::pair<T1, T2>>>(
            list<std::pair<T1, T2>>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename list<T2>::Nil>(_loop_l2->v())) {
          *(_write) = std::make_unique<list<std::pair<T1, T2>>>(
              list<std::pair<T1, T2>>::nil());
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename list<T2>::Cons>(_loop_l2->v());
          auto _cell = std::make_unique<list<std::pair<T1, T2>>>(
              typename list<std::pair<T1, T2>>::Cons(
                  std::make_pair(d_a0, d_a00), nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename list<std::pair<T1, T2>>::Cons>(
                        (*_write)->v_mut())
                        .d_a1;
          _loop_l2 = d_a10.get();
          _loop_l1 = d_a1.get();
          continue;
        }
      }
    }
    return std::move(*(_head));
  } /// zip3 combines three lists.

  template <typename T1, typename T2, typename T3>
  static list<std::pair<T1, std::pair<T2, T3>>>
  zip3(const list<T1> &l1, const list<T2> &l2, const list<T3> &l3) {
    std::unique_ptr<list<std::pair<T1, std::pair<T2, T3>>>> _head{};
    std::unique_ptr<list<std::pair<T1, std::pair<T2, T3>>>> *_write = &_head;
    const list<T3> *_loop_l3 = &l3;
    const list<T2> *_loop_l2 = &l2;
    const list<T1> *_loop_l1 = &l1;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l1->v())) {
        *(_write) = std::make_unique<list<std::pair<T1, std::pair<T2, T3>>>>(
            list<std::pair<T1, std::pair<T2, T3>>>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l1->v());
        if (std::holds_alternative<typename list<T2>::Nil>(_loop_l2->v())) {
          *(_write) = std::make_unique<list<std::pair<T1, std::pair<T2, T3>>>>(
              list<std::pair<T1, std::pair<T2, T3>>>::nil());
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename list<T2>::Cons>(_loop_l2->v());
          if (std::holds_alternative<typename list<T3>::Nil>(_loop_l3->v())) {
            *(_write) =
                std::make_unique<list<std::pair<T1, std::pair<T2, T3>>>>(
                    list<std::pair<T1, std::pair<T2, T3>>>::nil());
            break;
          } else {
            const auto &[d_a01, d_a11] =
                std::get<typename list<T3>::Cons>(_loop_l3->v());
            auto _cell =
                std::make_unique<list<std::pair<T1, std::pair<T2, T3>>>>(
                    typename list<std::pair<T1, std::pair<T2, T3>>>::Cons(
                        std::make_pair(d_a0, std::make_pair(d_a00, d_a01)),
                        nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<
                     typename list<std::pair<T1, std::pair<T2, T3>>>::Cons>(
                     (*_write)->v_mut())
                     .d_a1;
            _loop_l3 = d_a11.get();
            _loop_l2 = d_a10.get();
            _loop_l1 = d_a1.get();
            continue;
          }
        }
      }
    }
    return std::move(*(_head));
  }

  /// split_at n l splits at position n.
  template <typename T1>
  static std::pair<list<T1>, list<T1>>
  split_at(const unsigned int n,
           list<T1> l) { /// _Enter: captures varying parameters for each
                         /// recursive call.

    struct _Enter {
      list<T1> l;
      unsigned int n;
    };

    /// _Cont_Cons: saves [d_a0], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      T1 d_a0;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    std::pair<list<T1>, list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{l, n});
    /// Loopified split_at: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        list<T1> l = std::move(_f.l);
        const unsigned int n = _f.n;
        if (n <= 0) {
          _result = std::make_pair(list<T1>::nil(), std::move(l));
        } else {
          unsigned int m = n - 1;
          if (std::holds_alternative<typename list<T1>::Nil>(l.v_mut())) {
            _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
          } else {
            auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v_mut());
            _stack.emplace_back(_Cont_Cons{d_a0});
            _stack.emplace_back(_Enter{std::move(*(d_a1)), m});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        T1 d_a0 = _f.d_a0;
        const list<T1> &taken = _result.first;
        const list<T1> &rest = _result.second;
        _result = std::make_pair(list<T1>::cons(d_a0, taken), rest);
      }
    }
    return _result;
  }

  /// swizzle separates into even/odd positions.
  template <typename T1>
  static std::pair<list<T1>, list<T1>>
  swizzle(const list<T1> &l) { /// _Enter: captures varying parameters for each
                               /// recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Cont_Cons: saves [d_a0, d_a00], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Cons {
      T1 d_a0;
      T1 d_a00;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    std::pair<list<T1>, list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified swizzle: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *(_f.l);
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          auto &&_sv0 = *(d_a1);
          if (std::holds_alternative<typename list<T1>::Nil>(_sv0.v())) {
            _result = std::make_pair(list<T1>::cons(d_a0, list<T1>::nil()),
                                     list<T1>::nil());
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename list<T1>::Cons>(_sv0.v());
            _stack.emplace_back(_Cont_Cons{d_a0, d_a00});
            _stack.emplace_back(_Enter{d_a10.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        T1 d_a0 = _f.d_a0;
        T1 d_a00 = _f.d_a00;
        const list<T1> &evens = _result.first;
        const list<T1> &odds = _result.second;
        _result = std::make_pair(list<T1>::cons(d_a0, evens),
                                 list<T1>::cons(d_a00, odds));
      }
    }
    return _result;
  }

  /// span p l splits at first element not satisfying p.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static std::pair<list<T1>, list<T1>>
  span(F0 &&p,
       const list<T1> &
           l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Cont1: saves [d_a0], resumes after recursive call, then processes rest.
    struct _Cont1 {
      T1 d_a0;
    };

    using _Frame = std::variant<_Enter, _Cont1>;
    std::pair<list<T1>, list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified span: _Enter -> _Cont1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *(_f.l);
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::make_pair(list<T1>::nil(), list<T1>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          if (p(d_a0)) {
            _stack.emplace_back(_Cont1{d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            _result =
                std::make_pair(list<T1>::nil(), list<T1>::cons(d_a0, *(d_a1)));
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont1>(_frame));
        T1 d_a0 = _f.d_a0;
        const list<T1> &ys = _result.first;
        const list<T1> &zs = _result.second;
        _result = std::make_pair(list<T1>::cons(d_a0, ys), zs);
      }
    }
    return _result;
  }

  /// partition3 pivot l three-way partition around pivot.
  static std::pair<list<unsigned int>,
                   std::pair<list<unsigned int>, list<unsigned int>>>
  partition3(const unsigned int pivot, const list<unsigned int> &l);
  /// min_max l finds both min and max in one pass.
  static std::pair<unsigned int, unsigned int>
  min_max(const list<unsigned int> &l);
  /// sum_and_count computes both in one pass.
  static std::pair<unsigned int, unsigned int>
  sum_and_count(const list<unsigned int> &l);
  /// sum_prod_count triple accumulator.
  static std::pair<unsigned int, std::pair<unsigned int, unsigned int>>
  sum_prod_count(const list<unsigned int> &l);

  /// mapAccumL f acc l map with accumulator threading.
  template <typename F0>
    requires std::is_invocable_r_v<std::pair<unsigned int, unsigned int>, F0 &,
                                   unsigned int &, unsigned int &>
  static std::pair<unsigned int, list<unsigned int>> mapAccumL(
      F0 &&f, const unsigned int acc,
      const list<unsigned int>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const list<unsigned int> *l;
      unsigned int acc;
    };

    /// _Cont_acc_: saves [y], resumes after recursive call, then processes
    /// rest.
    struct _Cont_acc_ {
      unsigned int y;
    };

    using _Frame = std::variant<_Enter, _Cont_acc_>;
    std::pair<unsigned int, list<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l, acc});
    /// Loopified mapAccumL: _Enter -> _Cont_acc_.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<unsigned int> &l = *(_f.l);
        const unsigned int acc = _f.acc;
        if (std::holds_alternative<typename list<unsigned int>::Nil>(l.v())) {
          _result = std::make_pair(acc, list<unsigned int>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename list<unsigned int>::Cons>(l.v());
          auto _cs = f(acc, d_a0);
          const unsigned int &acc_ = _cs.first;
          const unsigned int &y = _cs.second;
          _stack.emplace_back(_Cont_acc_{y});
          _stack.emplace_back(_Enter{d_a1.get(), acc_});
        }
      } else {
        auto _f = std::move(std::get<_Cont_acc_>(_frame));
        unsigned int y = _f.y;
        const unsigned int &final_acc = _result.first;
        const list<unsigned int> &ys = _result.second;
        _result = std::make_pair(final_acc, list<unsigned int>::cons(y, ys));
      }
    }
    return _result;
  }

  /// lookup_all key l finds all values associated with key.
  static list<unsigned int>
  lookup_all(const unsigned int key,
             const list<std::pair<unsigned int, unsigned int>> &l);
  /// swap_pairs l swaps elements in each pair.
  static list<std::pair<unsigned int, unsigned int>>
  swap_pairs(const list<std::pair<unsigned int, unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_PAIRS
