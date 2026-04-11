#ifndef INCLUDED_LOOPIFY_TAIL
#define INCLUDED_LOOPIFY_TAIL

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct LoopifyTail {
  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::shared_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit list(Nil _v) : d_v_(std::move(_v)) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<list<t_A>> nil() {
      return std::make_shared<list<t_A>>(Nil{});
    }

    static std::shared_ptr<list<t_A>>
    cons(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
      return std::make_shared<list<t_A>>(Cons{std::move(a0), a1});
    }

    static std::shared_ptr<list<t_A>> cons(t_A a0,
                                           std::shared_ptr<list<t_A>> &&a1) {
      return std::make_shared<list<t_A>>(Cons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename list<T1>::Cons &>().d_a1) _s0;
      decltype(std::declval<const typename list<T1>::Cons &>().d_a0) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list<T1>::Nil) -> void {
                          _result = f;
                        },
                        [&](const typename list<T1>::Cons _args) -> void {
                          _stack.push_back(_Call1{_args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = f0(_f._s1, _f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename list<T1>::Cons &>().d_a1) _s0;
      decltype(std::declval<const typename list<T1>::Cons &>().d_a0) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list<T1>::Nil) -> void {
                          _result = f;
                        },
                        [&](const typename list<T1>::Cons _args) -> void {
                          _stack.push_back(_Call1{_args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = f0(_f._s1, _f._s0, _result); }},
          _frame);
    }
    return _result;
  } /// Tail-recursive: last element of a list

  template <typename T1>
  static T1 last(const T1 x, const std::shared_ptr<list<T1>> &l) {
    T1 _result;
    std::shared_ptr<list<T1>> _loop_l = l;
    T1 _loop_x = x;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename list<T1>::Nil) {
                              _result = _loop_x;
                              _continue = false;
                            },
                            [&](const typename list<T1>::Cons _args) {
                              std::shared_ptr<list<T1>> _next_l = _args.d_a1;
                              T1 _next_x = _args.d_a0;
                              _loop_l = std::move(_next_l);
                              _loop_x = std::move(_next_x);
                            }},
                 _loop_l->v());
    }
    return _result;
  } /// Tail-recursive: length with accumulator

  template <typename T1>
  __attribute__((pure)) static unsigned int
  length_acc(const unsigned int acc, const std::shared_ptr<list<T1>> &l) {
    unsigned int _result;
    std::shared_ptr<list<T1>> _loop_l = l;
    unsigned int _loop_acc = acc;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename list<T1>::Nil) {
                              _result = _loop_acc;
                              _continue = false;
                            },
                            [&](const typename list<T1>::Cons _args) {
                              std::shared_ptr<list<T1>> _next_l = _args.d_a1;
                              unsigned int _next_acc = (_loop_acc + 1);
                              _loop_l = std::move(_next_l);
                              _loop_acc = std::move(_next_acc);
                            }},
                 _loop_l->v());
    }
    return _result;
  }

  template <typename T1>
  __attribute__((pure)) static unsigned int
  length(const std::shared_ptr<list<T1>> &l) {
    return length_acc<T1>(0u, l);
  }

  /// Tail-recursive: membership test
  __attribute__((pure)) static bool
  member(const unsigned int x, const std::shared_ptr<list<unsigned int>> &l);
  /// Tail-recursive: nth element
  __attribute__((pure)) static unsigned int
  nth(const unsigned int n, const std::shared_ptr<list<unsigned int>> &l,
      const unsigned int default0);

  /// Tail-recursive: fold_left
  template <typename T1, typename T2, MapsTo<T2, T2, T1> F0>
  static T2 fold_left(F0 &&f, const T2 acc,
                      const std::shared_ptr<list<T1>> &l) {
    T2 _result;
    std::shared_ptr<list<T1>> _loop_l = l;
    T2 _loop_acc = acc;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename list<T1>::Nil) {
                              _result = _loop_acc;
                              _continue = false;
                            },
                            [&](const typename list<T1>::Cons _args) {
                              std::shared_ptr<list<T1>> _next_l = _args.d_a1;
                              T2 _next_acc = f(_loop_acc, _args.d_a0);
                              _loop_l = std::move(_next_l);
                              _loop_acc = std::move(_next_acc);
                            }},
                 _loop_l->v());
    }
    return _result;
  }

  /// Tail-recursive: lookup in association list
  __attribute__((pure)) static unsigned int
  lookup(const unsigned int key,
         const std::shared_ptr<list<std::pair<unsigned int, unsigned int>>> &l);
};

#endif // INCLUDED_LOOPIFY_TAIL
