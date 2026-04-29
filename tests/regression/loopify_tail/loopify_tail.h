#ifndef INCLUDED_LOOPIFY_TAIL
#define INCLUDED_LOOPIFY_TAIL

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct LoopifyTail {
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
    __attribute__((pure)) list<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Nil>(_sv.v())) {
        return list<t_A>(Nil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
        return list<t_A>(Cons{
            d_a0, d_a1 ? std::make_unique<LoopifyTail::list<t_A>>(d_a1->clone())
                       : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        d_v_ = Nil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<_U>::Cons>(_other.v());
        d_v_ = Cons{t_A(d_a0),
                    d_a1 ? std::make_unique<list<t_A>>(*d_a1) : nullptr};
      }
    }

    __attribute__((pure)) static list<t_A> nil() { return list(Nil{}); }

    __attribute__((pure)) static list<t_A> cons(t_A a0, list<t_A> a1) {
      return list(
          Cons{std::move(a0), std::make_unique<list<t_A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      std::vector<std::unique_ptr<list>> _stack;
      auto _drain = [&](list &_node) {
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
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
    };

    struct _Call1 {
      list<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
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

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
    };

    struct _Call1 {
      list<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{*(d_a1), d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  } /// Tail-recursive: last element of a list

  template <typename T1> static T1 last(const T1 x, const list<T1> &l) {
    T1 _result;
    list<T1> _loop_l = l;
    T1 _loop_x = x;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        _result = _loop_x;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        list<T1> _next_l = *(d_a1);
        T1 _next_x = d_a0;
        _loop_l = std::move(_next_l);
        _loop_x = std::move(_next_x);
      }
    }
    return _result;
  } /// Tail-recursive: length with accumulator

  template <typename T1>
  __attribute__((pure)) static unsigned int length_acc(unsigned int acc,
                                                       const list<T1> &l) {
    unsigned int _result;
    list<T1> _loop_l = l;
    unsigned int _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        _result = _loop_acc;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        list<T1> _next_l = *(d_a1);
        unsigned int _next_acc = (_loop_acc + 1);
        _loop_l = std::move(_next_l);
        _loop_acc = std::move(_next_acc);
      }
    }
    return _result;
  }

  template <typename T1>
  __attribute__((pure)) static unsigned int length(const list<T1> &l) {
    return length_acc<T1>(0u, l);
  }

  /// Tail-recursive: membership test
  __attribute__((pure)) static bool member(const unsigned int &x,
                                           const list<unsigned int> &l);
  /// Tail-recursive: nth element
  __attribute__((pure)) static unsigned int nth(const unsigned int &n,
                                                const list<unsigned int> &l,
                                                unsigned int default0);

  /// Tail-recursive: fold_left
  template <typename T1, typename T2, MapsTo<T2, T2, T1> F0>
  static T2 fold_left(F0 &&f, const T2 acc, const list<T1> &l) {
    T2 _result;
    list<T1> _loop_l = l;
    T2 _loop_acc = acc;
    while (true) {
      if (std::holds_alternative<typename list<T1>::Nil>(_loop_l.v())) {
        _result = _loop_acc;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<T1>::Cons>(_loop_l.v());
        list<T1> _next_l = *(d_a1);
        T2 _next_acc = f(_loop_acc, d_a0);
        _loop_l = std::move(_next_l);
        _loop_acc = std::move(_next_acc);
      }
    }
    return _result;
  }

  /// Tail-recursive: lookup in association list
  __attribute__((pure)) static unsigned int
  lookup(const unsigned int &key,
         const list<std::pair<unsigned int, unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_TAIL
