#ifndef INCLUDED_LOOPIFY_PREDICATES
#define INCLUDED_LOOPIFY_PREDICATES

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
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

struct LoopifyPredicates {
  template <MapsTo<bool, unsigned int> F0>
  static List<unsigned int> take_while(F0 &&p, const List<unsigned int> &l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    const List<unsigned int> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(d_a0)) {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = d_a1.get();
          continue;
        } else {
          *(_write) =
              std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
          break;
        }
      }
    }
    return std::move(*(_head));
  }

  template <MapsTo<bool, unsigned int> F0>
  static List<unsigned int> drop_while(F0 &&p, List<unsigned int> l) {
    List<unsigned int> _result;
    List<unsigned int> _loop_l = std::move(l);
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v_mut())) {
        _result = List<unsigned int>::nil();
        break;
      } else {
        auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v_mut());
        if (p(d_a0)) {
          _loop_l = std::move(*(d_a1));
        } else {
          _result = _loop_l;
          break;
        }
      }
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::pair<List<unsigned int>, List<unsigned int>>
  span(F0 &&p, List<unsigned int> l) {
    struct _Enter {
      List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<List<unsigned int>, List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
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
          auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v_mut());
          if (p(d_a0)) {
            _stack.emplace_back(_Call1{d_a0});
            _stack.emplace_back(_Enter{*(d_a1)});
          } else {
            _result = std::make_pair(List<unsigned int>::nil(), l);
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int d_a0 = std::move(_f._s0);
        const List<unsigned int> &yes = _result.first;
        const List<unsigned int> &no = _result.second;
        _result = std::make_pair(List<unsigned int>::cons(d_a0, yes), no);
      }
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::pair<List<unsigned int>, List<unsigned int>>
  break_at(F0 &&p, List<unsigned int> l) {
    struct _Enter {
      List<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<List<unsigned int>, List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
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
          auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v_mut());
          if (p(d_a0)) {
            _result = std::make_pair(List<unsigned int>::nil(), l);
          } else {
            _stack.emplace_back(_Call1{d_a0});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int d_a0 = std::move(_f._s0);
        const List<unsigned int> &before = _result.first;
        const List<unsigned int> &after = _result.second;
        _result = std::make_pair(List<unsigned int>::cons(d_a0, before), after);
      }
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  static List<unsigned int> filter(F0 &&p, const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      if (p(d_a0)) {
        return List<unsigned int>::cons(d_a0, filter(p, *(d_a1)));
      } else {
        return filter(p, *(d_a1));
      }
    }
  }

  template <MapsTo<bool, unsigned int> F0>
  static List<unsigned int> reject(F0 &&p, const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      if (p(d_a0)) {
        return reject(p, *(d_a1));
      } else {
        return List<unsigned int>::cons(d_a0, reject(p, *(d_a1)));
      }
    }
  }

  template <MapsTo<bool, unsigned int> F0>
  static bool forall_pred(F0 &&p, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> *l;
    };

    struct _Call1 {
      bool _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{&l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *(_f.l);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = true;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Call1{p(d_a0)});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = (_f._s0 && _result);
      }
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  static bool exists_pred(F0 &&p, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> *l;
    };

    struct _Call1 {
      bool _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{&l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *(_f.l);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = false;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Call1{p(d_a0)});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = (_f._s0 || _result);
      }
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
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
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(d_a0)) {
          _result = std::make_optional<unsigned int>(_loop_idx);
          break;
        } else {
          unsigned int _next_idx = (_loop_idx + 1u);
          const List<unsigned int> *_next_l = d_a1.get();
          _loop_idx = std::move(_next_idx);
          _loop_l = _next_l;
        }
      }
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::optional<unsigned int> find_index(F0 &&p,
                                                const List<unsigned int> &l) {
    return find_index_aux(p, l, 0u);
  }

  template <MapsTo<bool, unsigned int> F0>
  static List<unsigned int>
  find_indices_aux(F0 &&p, const List<unsigned int> &l, unsigned int idx) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      if (p(d_a0)) {
        return List<unsigned int>::cons(
            idx, find_indices_aux(p, *(d_a1), (idx + 1u)));
      } else {
        return find_indices_aux(p, *(d_a1), (idx + 1u));
      }
    }
  }

  template <MapsTo<bool, unsigned int> F0>
  static List<unsigned int> find_indices(F0 &&p, const List<unsigned int> &l) {
    return find_indices_aux(p, l, 0u);
  }

  template <MapsTo<bool, unsigned int, unsigned int> F0>
  static List<unsigned int> delete_by(F0 &&eq, const unsigned int &x,
                                      const List<unsigned int> &l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    const List<unsigned int> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (eq(x, d_a0)) {
          *(_write) = std::make_unique<List<unsigned int>>(*(d_a1));
          break;
        } else {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = d_a1.get();
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  static List<unsigned int> remove_all(const unsigned int &x,
                                       const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_PREDICATES
