#ifndef INCLUDED_LOOPIFY_ADVANCED_LISTS
#define INCLUDED_LOOPIFY_ADVANCED_LISTS

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

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    std::shared_ptr<List<t_A>> _head{};
    std::shared_ptr<List<t_A>> _last{};
    const List *_loop_self = this;
    bool _continue = true;
    while (_continue) {
      if (std::holds_alternative<typename List<t_A>::Nil>(_loop_self->v())) {
        if (_last) {
          std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = m;
        } else {
          _head = m;
        }
        _continue = false;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<t_A>::Cons>(_loop_self->v());
        auto _cell = List<t_A>::cons(d_a0, nullptr);
        if (_last) {
          std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_self = d_a1.get();
        continue;
      }
    }
    return _head;
  }
};

struct LoopifyAdvancedLists {
  __attribute__((pure)) static unsigned int
  product(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  compress(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  pairwise_sum(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  group_pairs(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  interleave(std::shared_ptr<List<unsigned int>> l1,
             std::shared_ptr<List<unsigned int>> l2);
  static std::shared_ptr<List<unsigned int>> concat_lists(
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);

  template <MapsTo<std::shared_ptr<List<unsigned int>>, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  flat_map(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      std::shared_ptr<List<unsigned int>> _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<List<unsigned int>> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
          _result = List<unsigned int>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l->v());
          _stack.emplace_back(_Call1{f(d_a0)});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = _f._s0->app(_result);
      }
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool
  all_satisfy(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      bool _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    bool _result{};
    std::vector<_Frame> _stack;
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
  any_satisfy(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      bool _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    bool _result{};
    std::vector<_Frame> _stack;
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
  find_first(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    std::optional<unsigned int> _result;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        _result = std::optional<unsigned int>();
        _continue = false;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(d_a0)) {
          _result = std::make_optional<unsigned int>(d_a0);
          _continue = false;
        } else {
          _loop_l = d_a1;
        }
      }
    }
    return _result;
  }
};

#endif // INCLUDED_LOOPIFY_ADVANCED_LISTS
