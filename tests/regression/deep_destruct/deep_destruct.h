#ifndef INCLUDED_DEEP_DESTRUCT
#define INCLUDED_DEEP_DESTRUCT

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

struct DeepDestruct {
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
    explicit mylist(Mynil _v) : d_v_(_v) {}

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
    _stack.emplace_back(_Enter{m});
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
                          _stack.emplace_back(_Call1{_args.d_a1, _args.d_a0});
                          _stack.emplace_back(_Enter{_args.d_a1});
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
    _stack.emplace_back(_Enter{m});
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
                          _stack.emplace_back(_Call1{_args.d_a1, _args.d_a0});
                          _stack.emplace_back(_Enter{_args.d_a1});
                        }},
                    m->v());
              },
              [&](_Call1 _f) { _result = f0(_f._s1, _f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  /// Tail-recursive list builder — should compile to a loop.
  static std::shared_ptr<mylist<unsigned int>>
  build_aux(const unsigned int n, std::shared_ptr<mylist<unsigned int>> acc);
  static std::shared_ptr<mylist<unsigned int>> build(const unsigned int n);
  /// Simple accessor to observe the result.
  __attribute__((pure)) static unsigned int
  head_or_zero(const std::shared_ptr<mylist<unsigned int>> &l);
};

#endif // INCLUDED_DEEP_DESTRUCT
