#ifndef INCLUDED_LOOPIFY_PREDICATES
#define INCLUDED_LOOPIFY_PREDICATES

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
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

struct LoopifyPredicates {
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static List<unsigned int> take_while(F0 &&p, const List<unsigned int> &l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    const List<unsigned int> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .a1;
          _loop_l = a1.get();
          continue;
        } else {
          *_write =
              std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
          break;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static List<unsigned int> drop_while(F0 &&p, List<unsigned int> l) {
    List<unsigned int> _result;
    List<unsigned int> _loop_l = std::move(l);
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v_mut())) {
        _result = List<unsigned int>::nil();
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v_mut());
        if (p(std::move(a0))) {
          _loop_l = std::move(*a1);
        } else {
          _result = _loop_l;
          break;
        }
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static std::pair<List<unsigned int>, List<unsigned int>>
  span(F0 &&p,
       List<unsigned int>
           l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      List<unsigned int> l;
    };

    /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
    struct _Cont1 {
      unsigned int a0;
    };

    using _Frame = std::variant<_Enter, _Cont1>;
    std::pair<List<unsigned int>, List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{l});
    /// Loopified span: _Enter -> _Cont1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        List<unsigned int> l = std::move(_f.l);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                l.v_mut())) {
          _result = std::make_pair(List<unsigned int>::nil(),
                                   List<unsigned int>::nil());
        } else {
          auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v_mut());
          if (p(a0)) {
            _stack.emplace_back(_Cont1{a0});
            _stack.emplace_back(_Enter{std::move(*a1)});
          } else {
            _result = std::make_pair(List<unsigned int>::nil(), l);
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont1>(_frame));
        unsigned int a0 = _f.a0;
        const List<unsigned int> &yes = _result.first;
        const List<unsigned int> &no = _result.second;
        _result =
            std::make_pair(List<unsigned int>::cons(std::move(a0), yes), no);
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static std::pair<List<unsigned int>, List<unsigned int>>
  break_at(F0 &&p,
           List<unsigned int> l) { /// _Enter: captures varying parameters for
                                   /// each recursive call.

    struct _Enter {
      List<unsigned int> l;
    };

    /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
    struct _Cont1 {
      unsigned int a0;
    };

    using _Frame = std::variant<_Enter, _Cont1>;
    std::pair<List<unsigned int>, List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{l});
    /// Loopified break_at: _Enter -> _Cont1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        List<unsigned int> l = std::move(_f.l);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                l.v_mut())) {
          _result = std::make_pair(List<unsigned int>::nil(),
                                   List<unsigned int>::nil());
        } else {
          auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v_mut());
          if (p(a0)) {
            _result = std::make_pair(List<unsigned int>::nil(), l);
          } else {
            _stack.emplace_back(_Cont1{a0});
            _stack.emplace_back(_Enter{std::move(*a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont1>(_frame));
        unsigned int a0 = _f.a0;
        const List<unsigned int> &before = _result.first;
        const List<unsigned int> &after = _result.second;
        _result = std::make_pair(
            List<unsigned int>::cons(std::move(a0), before), after);
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static List<unsigned int> filter(F0 &&p, const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
      if (p(a0)) {
        return List<unsigned int>::cons(a0, filter(p, *a1));
      } else {
        return filter(p, *a1);
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static List<unsigned int> reject(F0 &&p, const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
      if (p(a0)) {
        return reject(p, *a1);
      } else {
        return List<unsigned int>::cons(a0, reject(p, *a1));
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static bool forall_pred(
      F0 &&p,
      const List<unsigned int>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      bool a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified forall_pred: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *_f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = true;
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{p(a0)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_f.a0 && _result);
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static bool exists_pred(
      F0 &&p,
      const List<unsigned int>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      bool a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified exists_pred: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *_f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = false;
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{p(a0)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_f.a0 || _result);
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static std::optional<unsigned int>
  find_index_aux(F0 &&p, const List<unsigned int> &l, unsigned int idx) {
    std::optional<unsigned int> _result;
    unsigned int _loop_idx = std::move(idx);
    const List<unsigned int> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        _result = std::optional<unsigned int>();
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(a0)) {
          _result = std::make_optional<unsigned int>(_loop_idx);
          break;
        } else {
          _loop_idx = (_loop_idx + 1u);
          _loop_l = a1.get();
        }
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static std::optional<unsigned int> find_index(F0 &&p,
                                                const List<unsigned int> &l) {
    return find_index_aux(p, l, 0u);
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static List<unsigned int>
  find_indices_aux(F0 &&p, const List<unsigned int> &l, unsigned int idx) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
      if (p(a0)) {
        return List<unsigned int>::cons(idx,
                                        find_indices_aux(p, *a1, (idx + 1u)));
      } else {
        return find_indices_aux(p, *a1, (idx + 1u));
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static List<unsigned int> find_indices(F0 &&p, const List<unsigned int> &l) {
    return find_indices_aux(p, l, 0u);
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &, unsigned int &>
  static List<unsigned int> delete_by(F0 &&eq, unsigned int x,
                                      const List<unsigned int> &l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    const List<unsigned int> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (eq(x, a0)) {
          *_write = std::make_unique<List<unsigned int>>(*a1);
          break;
        } else {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .a1;
          _loop_l = a1.get();
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  static List<unsigned int> remove_all(unsigned int x,
                                       const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_PREDICATES
