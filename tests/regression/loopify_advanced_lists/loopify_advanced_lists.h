#ifndef INCLUDED_LOOPIFY_ADVANCED_LISTS
#define INCLUDED_LOOPIFY_ADVANCED_LISTS

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
  List clone() const {
    List _out{};

    struct _CloneFrame {
      const List *_src;
      List *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List *_src = _frame._src;
      List *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ =
            Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<List>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1)
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
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
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
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
  const variant_t &v() const { return d_v_; }

  List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    List<t_A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        const List *_next_self = d_a1.get();
        List<t_A> _next_m = std::move(_loop_m);
        _loop_self = _next_self;
        _loop_m = std::move(_next_m);
        continue;
      }
    }
    return std::move(*(_head));
  }
};

struct LoopifyAdvancedLists {
  static unsigned int product(const List<unsigned int> &l);
  static List<unsigned int> compress(const List<unsigned int> &l);
  static List<unsigned int> pairwise_sum(const List<unsigned int> &l);
  static List<std::pair<unsigned int, unsigned int>>
  group_pairs(const List<unsigned int> &l);
  static List<unsigned int> interleave(List<unsigned int> l1,
                                       List<unsigned int> l2);
  static List<unsigned int> concat_lists(const List<List<unsigned int>> &ll);

  template <MapsTo<List<unsigned int>, unsigned int> F0>
  static List<unsigned int> flat_map(F0 &&f, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> *l;
    };

    struct _Call1 {
      List<unsigned int> _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    List<unsigned int> _result{};
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
          _result = List<unsigned int>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Call1{f(d_a0)});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = _f._s0.app(_result);
      }
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  static bool all_satisfy(F0 &&p, const List<unsigned int> &l) {
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
  static bool any_satisfy(F0 &&p, const List<unsigned int> &l) {
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
  static std::optional<unsigned int> find_first(F0 &&p,
                                                const List<unsigned int> &l) {
    std::optional<unsigned int> _result;
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
          _result = std::make_optional<unsigned int>(d_a0);
          break;
        } else {
          _loop_l = d_a1.get();
        }
      }
    }
    return _result;
  }
};

#endif // INCLUDED_LOOPIFY_ADVANCED_LISTS
