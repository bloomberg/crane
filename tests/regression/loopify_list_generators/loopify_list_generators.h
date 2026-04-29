#ifndef INCLUDED_LOOPIFY_LIST_GENERATORS
#define INCLUDED_LOOPIFY_LIST_GENERATORS

#include <functional>
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
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
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

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, List<t_A> a1) {
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
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    const List *_self = this;

    struct _Enter {
      const List *_self;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{_self});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List *_self = _f._self;
        auto &&_sv = *(_self);
        if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<t_A>::Cons>(_sv.v());
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

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
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
        _loop_self = std::move(_next_self);
        _loop_m = std::move(_next_m);
        continue;
      }
    }
    return std::move(*(_head));
  }
};

struct LoopifyListGenerators {
  __attribute__((pure)) static List<unsigned int>
  cycle_fuel(const unsigned int &fuel, const unsigned int &n,
             const List<unsigned int> &l);
  __attribute__((pure)) static List<unsigned int>
  cycle(const unsigned int &n, const List<unsigned int> &l);

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  iterate(F0 &&f, const unsigned int &n, unsigned int x) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    unsigned int _loop_x = std::move(x);
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        unsigned int n_ = _loop_n - 1;
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(_loop_x, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        unsigned int _next_x = f(_loop_x);
        unsigned int _next_n = n_;
        _loop_x = std::move(_next_x);
        _loop_n = std::move(_next_n);
        continue;
      }
    }
    return std::move(*(_head));
  }

  template <MapsTo<unsigned int, unsigned int> F2>
  __attribute__((pure)) static List<unsigned int>
  build_list_aux(const unsigned int &n, const unsigned int &idx, F2 &&f) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    unsigned int _loop_idx = idx;
    unsigned int _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        unsigned int n_ = _loop_n - 1;
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(f(_loop_idx), nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        unsigned int _next_idx = (_loop_idx + 1u);
        unsigned int _next_n = n_;
        _loop_idx = std::move(_next_idx);
        _loop_n = std::move(_next_n);
        continue;
      }
    }
    return std::move(*(_head));
  }

  template <MapsTo<unsigned int, unsigned int> F1>
  __attribute__((pure)) static List<unsigned int>
  build_list(const unsigned int &n, F1 &&f) {
    return build_list_aux(n, 0u, f);
  }

  template <MapsTo<unsigned int, unsigned int> F1>
  __attribute__((pure)) static List<unsigned int> init_list(unsigned int n,
                                                            F1 &&f) {
    if (n <= 0) {
      return List<unsigned int>::nil();
    } else {
      unsigned int n_ = n - 1;
      return List<unsigned int>::cons(f(0u), [&]() {
        std::function<List<unsigned int>(unsigned int)> go;
        go = [&](unsigned int i) -> List<unsigned int> {
          struct _Enter {
            unsigned int i;
          };
          struct _Call1 {
            decltype(f((((n - std::declval<unsigned int &>()) > n
                             ? 0
                             : (n - std::declval<unsigned int &>()))))) _s0;
          };
          using _Frame = std::variant<_Enter, _Call1>;
          List<unsigned int> _result{};
          std::vector<_Frame> _stack;
          _stack.reserve(16);
          _stack.emplace_back(_Enter{i});
          while (!_stack.empty()) {
            _Frame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<_Enter>(_frame)) {
              auto _f = std::move(std::get<_Enter>(_frame));
              unsigned int i = _f.i;
              if (i <= 0) {
                _result = List<unsigned int>::nil();
              } else {
                unsigned int i_ = i - 1;
                _stack.emplace_back(_Call1{f((((n - i) > n ? 0 : (n - i))))});
                _stack.emplace_back(_Enter{i_});
              }
            } else {
              auto _f = std::move(std::get<_Call1>(_frame));
              _result = List<unsigned int>::cons(_f._s0, _result);
            }
          }
          return _result;
        };
        return go(n_);
      }());
    }
  }

  __attribute__((pure)) static List<unsigned int>
  range(unsigned int start, const unsigned int &count);
  __attribute__((pure)) static List<unsigned int>
  replicate_elem(const unsigned int &n, unsigned int x);
  __attribute__((pure)) static List<unsigned int>
  replicate_each(const unsigned int &n, const List<unsigned int> &l);

  template <MapsTo<unsigned int, unsigned int> F1>
  __attribute__((pure)) static List<unsigned int>
  tabulate(const unsigned int &n, F1 &&f) {
    if (n <= 0) {
      return List<unsigned int>::nil();
    } else {
      unsigned int n_ = n - 1;
      std::function<List<unsigned int>(unsigned int)> aux;
      aux = [&](unsigned int idx) -> List<unsigned int> {
        struct _Enter {
          unsigned int idx;
        };
        struct _Call1 {
          decltype(List<unsigned int>::cons(f(std::declval<unsigned int &>()),
                                            List<unsigned int>::nil())) _s0;
        };
        using _Frame = std::variant<_Enter, _Call1>;
        List<unsigned int> _result{};
        std::vector<_Frame> _stack;
        _stack.reserve(16);
        _stack.emplace_back(_Enter{idx});
        while (!_stack.empty()) {
          _Frame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<_Enter>(_frame)) {
            auto _f = std::move(std::get<_Enter>(_frame));
            unsigned int idx = _f.idx;
            if (idx <= 0) {
              _result =
                  List<unsigned int>::cons(f(0u), List<unsigned int>::nil());
            } else {
              unsigned int idx_ = idx - 1;
              _stack.emplace_back(_Call1{
                  List<unsigned int>::cons(f(idx), List<unsigned int>::nil())});
              _stack.emplace_back(_Enter{idx_});
            }
          } else {
            auto _f = std::move(std::get<_Call1>(_frame));
            _result = _result.app(_f._s0);
          }
        }
        return _result;
      };
      return aux(n_);
    }
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  zip_with(F0 &&f, const List<unsigned int> &l1, const List<unsigned int> &l2) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    List<unsigned int> _loop_l2 = l2;
    List<unsigned int> _loop_l1 = l1;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l1.v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2.v())) {
          *(_write) =
              std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(f(d_a0, d_a00), nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          List<unsigned int> _next_l2 = *(d_a10);
          List<unsigned int> _next_l1 = *(d_a1);
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  __attribute__((pure)) static List<std::pair<unsigned int, unsigned int>>
  enumerate_aux(unsigned int idx, const List<unsigned int> &l);
  __attribute__((pure)) static List<std::pair<unsigned int, unsigned int>>
  enumerate(const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_GENERATORS
