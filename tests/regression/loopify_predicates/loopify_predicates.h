#ifndef INCLUDED_LOOPIFY_PREDICATES
#define INCLUDED_LOOPIFY_PREDICATES

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct LoopifyPredicates {
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  take_while(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> *_write = &_head;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write = List<unsigned int>::nil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(d_a0)) {
          auto _cell = List<unsigned int>::cons(d_a0, nullptr);
          *_write = _cell;
          _write =
              &std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1;
          _loop_l = d_a1;
          continue;
        } else {
          *_write = List<unsigned int>::nil();
          break;
        }
      }
    }
    return _head;
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  drop_while(F0 &&p, std::shared_ptr<List<unsigned int>> l) {
    std::shared_ptr<List<unsigned int>> _result;
    std::shared_ptr<List<unsigned int>> _loop_l = std::move(l);
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        _result = List<unsigned int>::nil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(d_a0)) {
          _loop_l = d_a1;
        } else {
          _result = std::move(_loop_l);
          break;
        }
      }
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  span(F0 &&p, std::shared_ptr<List<unsigned int>> l) {
    struct _Enter {
      std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<List<unsigned int>>,
              std::shared_ptr<List<unsigned int>>>
        _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        std::shared_ptr<List<unsigned int>> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
          _result = std::make_pair(List<unsigned int>::nil(),
                                   List<unsigned int>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l->v());
          if (p(d_a0)) {
            _stack.emplace_back(_Call1{d_a0});
            _stack.emplace_back(_Enter{d_a1});
          } else {
            _result = std::make_pair(List<unsigned int>::nil(), std::move(l));
          }
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        unsigned int d_a0 = _f._s0;
        const std::shared_ptr<List<unsigned int>> &yes = _result.first;
        const std::shared_ptr<List<unsigned int>> &no = _result.second;
        _result = std::make_pair(List<unsigned int>::cons(d_a0, yes), no);
      }
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  break_at(F0 &&p, std::shared_ptr<List<unsigned int>> l) {
    struct _Enter {
      std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<List<unsigned int>>,
              std::shared_ptr<List<unsigned int>>>
        _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        std::shared_ptr<List<unsigned int>> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
          _result = std::make_pair(List<unsigned int>::nil(),
                                   List<unsigned int>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l->v());
          if (p(d_a0)) {
            _result = std::make_pair(List<unsigned int>::nil(), std::move(l));
          } else {
            _stack.emplace_back(_Call1{d_a0});
            _stack.emplace_back(_Enter{d_a1});
          }
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        unsigned int d_a0 = _f._s0;
        const std::shared_ptr<List<unsigned int>> &before = _result.first;
        const std::shared_ptr<List<unsigned int>> &after = _result.second;
        _result = std::make_pair(List<unsigned int>::cons(d_a0, before), after);
      }
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  filter(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> *_write = &_head;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write = List<unsigned int>::nil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(d_a0)) {
          auto _cell = List<unsigned int>::cons(d_a0, nullptr);
          *_write = _cell;
          _write =
              &std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1;
          _loop_l = d_a1;
          continue;
        } else {
          _loop_l = d_a1;
          continue;
        }
      }
    }
    return _head;
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  reject(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> *_write = &_head;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write = List<unsigned int>::nil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(d_a0)) {
          _loop_l = d_a1;
          continue;
        } else {
          auto _cell = List<unsigned int>::cons(d_a0, nullptr);
          *_write = _cell;
          _write =
              &std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1;
          _loop_l = d_a1;
          continue;
        }
      }
    }
    return _head;
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool
  forall_pred(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      bool _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<List<unsigned int>> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
          _result = true;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l->v());
          _stack.emplace_back(_Call1{p(d_a0)});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = (_f._s0 && _result);
      }
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool
  exists_pred(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      bool _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<List<unsigned int>> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
          _result = false;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l->v());
          _stack.emplace_back(_Call1{p(d_a0)});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = (_f._s0 || _result);
      }
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::optional<unsigned int>
  find_index_aux(F0 &&p, const std::shared_ptr<List<unsigned int>> &l,
                 const unsigned int idx) {
    std::optional<unsigned int> _result;
    unsigned int _loop_idx = idx;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
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
          std::shared_ptr<List<unsigned int>> _next_l = d_a1;
          _loop_idx = std::move(_next_idx);
          _loop_l = std::move(_next_l);
        }
      }
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::optional<unsigned int>
  find_index(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    return find_index_aux(p, l, 0u);
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  find_indices_aux(F0 &&p, const std::shared_ptr<List<unsigned int>> &l,
                   const unsigned int idx) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> *_write = &_head;
    unsigned int _loop_idx = idx;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write = List<unsigned int>::nil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(d_a0)) {
          auto _cell = List<unsigned int>::cons(_loop_idx, nullptr);
          *_write = _cell;
          _write =
              &std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1;
          unsigned int _next_idx = (_loop_idx + 1u);
          std::shared_ptr<List<unsigned int>> _next_l = d_a1;
          _loop_idx = std::move(_next_idx);
          _loop_l = std::move(_next_l);
          continue;
        } else {
          unsigned int _next_idx = (_loop_idx + 1u);
          std::shared_ptr<List<unsigned int>> _next_l = d_a1;
          _loop_idx = std::move(_next_idx);
          _loop_l = std::move(_next_l);
          continue;
        }
      }
    }
    return _head;
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  find_indices(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    return find_indices_aux(p, l, 0u);
  }

  template <MapsTo<bool, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  delete_by(F0 &&eq, const unsigned int x,
            const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> *_write = &_head;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write = List<unsigned int>::nil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (eq(x, d_a0)) {
          *_write = d_a1;
          break;
        } else {
          auto _cell = List<unsigned int>::cons(d_a0, nullptr);
          *_write = _cell;
          _write =
              &std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1;
          _loop_l = d_a1;
          continue;
        }
      }
    }
    return _head;
  }

  static std::shared_ptr<List<unsigned int>>
  remove_all(const unsigned int x,
             const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_PREDICATES
