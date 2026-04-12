#ifndef INCLUDED_DEEP_APP
#define INCLUDED_DEEP_APP

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

struct DeepApp {
  template <typename t_A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      t_A d_a0;
      std::shared_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit mylist(Mynil _v) : d_v_(std::move(_v)) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<mylist<t_A>> mynil() {
      return std::make_shared<mylist<t_A>>(Mynil{});
    }

    static std::shared_ptr<mylist<t_A>>
    mycons(t_A a0, const std::shared_ptr<mylist<t_A>> &a1) {
      return std::make_shared<mylist<t_A>>(Mycons{std::move(a0), a1});
    }

    static std::shared_ptr<mylist<t_A>>
    mycons(t_A a0, std::shared_ptr<mylist<t_A>> &&a1) {
      return std::make_shared<mylist<t_A>>(
          Mycons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<mylist<T1>>, T2> F1>
  static T2 mylist_rect(const T2 f, F1 &&f0,
                        const std::shared_ptr<mylist<T1>> &m) {
    struct _Enter {
      const std::shared_ptr<mylist<T1>> m;
    };

    struct _Call1 {
      decltype(std::declval<const typename mylist<T1>::Mycons &>().d_a1) _s0;
      decltype(std::declval<const typename mylist<T1>::Mycons &>().d_a0) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{m});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<mylist<T1>> m = _f.m;
                std::visit(
                    Overloaded{
                        [&](const typename mylist<T1>::Mynil &) -> void {
                          _result = f;
                        },
                        [&](const typename mylist<T1>::Mycons &_args) -> void {
                          _stack.push_back(_Call1{_args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    m->v());
              },
              [&](_Call1 _f) { _result = f0(_f._s1, _f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<mylist<T1>>, T2> F1>
  static T2 mylist_rec(const T2 f, F1 &&f0,
                       const std::shared_ptr<mylist<T1>> &m) {
    struct _Enter {
      const std::shared_ptr<mylist<T1>> m;
    };

    struct _Call1 {
      decltype(std::declval<const typename mylist<T1>::Mycons &>().d_a1) _s0;
      decltype(std::declval<const typename mylist<T1>::Mycons &>().d_a0) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{m});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<mylist<T1>> m = _f.m;
                std::visit(
                    Overloaded{
                        [&](const typename mylist<T1>::Mynil &) -> void {
                          _result = f;
                        },
                        [&](const typename mylist<T1>::Mycons &_args) -> void {
                          _stack.push_back(_Call1{_args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    m->v());
              },
              [&](_Call1 _f) { _result = f0(_f._s1, _f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  /// Tail-recursive builder — loopified.
  static std::shared_ptr<mylist<unsigned int>>
  build(const unsigned int n, std::shared_ptr<mylist<unsigned int>> acc);

  /// Recursive app — NOT tail-recursive, so loopification won't help
  /// unless TMC kicks in.  Even with TMC, the destructor chain for
  /// the result is still deep.
  template <typename T1>
  static std::shared_ptr<mylist<T1>> app(const std::shared_ptr<mylist<T1>> &l1,
                                         std::shared_ptr<mylist<T1>> l2) {
    std::shared_ptr<mylist<T1>> _head{};
    std::shared_ptr<mylist<T1>> _last{};
    std::shared_ptr<mylist<T1>> _loop_l1 = l1;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename mylist<T1>::Mynil &) {
                if (_last) {
                  std::get<typename mylist<T1>::Mycons>(_last->v_mut()).d_a1 =
                      std::move(l2);
                } else {
                  _head = std::move(l2);
                }
                _continue = false;
              },
              [&](const typename mylist<T1>::Mycons &_args) {
                auto _cell = mylist<T1>::mycons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename mylist<T1>::Mycons>(_last->v_mut()).d_a1 =
                      _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_l1 = _args.d_a1;
              }},
          _loop_l1->v());
    }
    return _head;
  } /// Recursive map — same issue.

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<mylist<T2>> map(F0 &&f,
                                         const std::shared_ptr<mylist<T1>> &l) {
    std::shared_ptr<mylist<T2>> _head{};
    std::shared_ptr<mylist<T2>> _last{};
    std::shared_ptr<mylist<T1>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename mylist<T1>::Mynil &) {
                if (_last) {
                  std::get<typename mylist<T2>::Mycons>(_last->v_mut()).d_a1 =
                      mylist<T2>::mynil();
                } else {
                  _head = mylist<T2>::mynil();
                }
                _continue = false;
              },
              [&](const typename mylist<T1>::Mycons &_args) {
                auto _cell = mylist<T2>::mycons(f(_args.d_a0), nullptr);
                if (_last) {
                  std::get<typename mylist<T2>::Mycons>(_last->v_mut()).d_a1 =
                      _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_l = _args.d_a1;
              }},
          _loop_l->v());
    }
    return _head;
  }

  /// Identity map to force traversal.
  static std::shared_ptr<mylist<unsigned int>>
  map_id(const std::shared_ptr<mylist<unsigned int>> &l);
  /// Append two lists.
  static std::shared_ptr<mylist<unsigned int>>
  append_lists(const std::shared_ptr<mylist<unsigned int>> &_x0,
               const std::shared_ptr<mylist<unsigned int>> &_x1);
  __attribute__((pure)) static unsigned int
  head_or_zero(const std::shared_ptr<mylist<unsigned int>> &l);

  template <typename T1>
  __attribute__((pure)) static unsigned int
  length(const std::shared_ptr<mylist<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<mylist<T1>> l;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<mylist<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename mylist<T1>::Mynil &) -> void {
                          _result = 0u;
                        },
                        [&](const typename mylist<T1>::Mycons &_args) -> void {
                          _stack.push_back(_Call1{});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1) { _result = (_result + 1); }},
          _frame);
    }
    return _result;
  }
};

#endif // INCLUDED_DEEP_APP
