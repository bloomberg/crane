#ifndef INCLUDED_LOOPIFY_LIST_TRANSFORMS
#define INCLUDED_LOOPIFY_LIST_TRANSFORMS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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

  __attribute__((pure)) unsigned int length() const {
    const List *_self = this;

    struct _Enter {
      const List *_self;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const List *_self = _f._self;
        if (std::holds_alternative<typename List<t_A>::Nil>(_self->v())) {
          _result = 0u;
        } else {
          const auto &_m = *std::get_if<typename List<t_A>::Cons>(&_self->v());
          _stack.emplace_back(_Call1{});
          _stack.emplace_back(_Enter{_m.d_a1.get()});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = (_result + 1);
      }
    }
    return _result;
  }

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
        const auto &_m =
            *std::get_if<typename List<t_A>::Cons>(&_loop_self->v());
        auto _cell = List<t_A>::cons(_m.d_a0, nullptr);
        if (_last) {
          std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_self = _m.d_a1.get();
        continue;
      }
    }
    return _head;
  }
};

struct LoopifyListTransforms {
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  run_length_encode(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  prefix_sums(const unsigned int acc,
              const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  sliding_pairs_fuel(const unsigned int fuel,
                     const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  sliding_pairs(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int abs_diff(const unsigned int x,
                                                     const unsigned int y);
  static std::shared_ptr<List<unsigned int>>
  differences_fuel(const unsigned int fuel,
                   const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  differences(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  take(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  drop(const unsigned int n, std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  chunks_of_fuel(const unsigned int fuel, const unsigned int n,
                 const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  chunks_of(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  rotate_left_fuel(const unsigned int fuel, const unsigned int n,
                   std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<List<unsigned int>>
  rotate_left(const unsigned int n,
              const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  uniq_sorted_fuel(const unsigned int fuel,
                   const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  uniq_sorted(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  step_sum(const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_TRANSFORMS
