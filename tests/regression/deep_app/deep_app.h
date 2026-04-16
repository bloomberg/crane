#ifndef INCLUDED_DEEP_APP
#define INCLUDED_DEEP_APP

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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
      std::shared_ptr<mylist<T1>> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{m});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<mylist<T1>> m = _f.m;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m->v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<T1>::Mycons>(m->v());
          _stack.emplace_back(_Call1{d_a1, d_a0});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = f0(_f._s1, _f._s0, _result);
      }
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
      std::shared_ptr<mylist<T1>> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{m});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<mylist<T1>> m = _f.m;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(m->v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<T1>::Mycons>(m->v());
          _stack.emplace_back(_Call1{d_a1, d_a0});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = f0(_f._s1, _f._s0, _result);
      }
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
    std::shared_ptr<mylist<T1>> *_write = &_head;
    std::shared_ptr<mylist<T1>> _loop_l1 = l1;
    while (true) {
      if (std::holds_alternative<typename mylist<T1>::Mynil>(_loop_l1->v())) {
        *_write = std::move(l2);
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<T1>::Mycons>(_loop_l1->v());
        auto _cell = mylist<T1>::mycons(d_a0, nullptr);
        *_write = _cell;
        _write = &std::get<typename mylist<T1>::Mycons>(_cell->v_mut()).d_a1;
        _loop_l1 = d_a1;
        continue;
      }
    }
    return _head;
  } /// Recursive map — same issue.

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<mylist<T2>> map(F0 &&f,
                                         const std::shared_ptr<mylist<T1>> &l) {
    std::shared_ptr<mylist<T2>> _head{};
    std::shared_ptr<mylist<T2>> *_write = &_head;
    std::shared_ptr<mylist<T1>> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename mylist<T1>::Mynil>(_loop_l->v())) {
        *_write = mylist<T2>::mynil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<T1>::Mycons>(_loop_l->v());
        auto _cell = mylist<T2>::mycons(f(d_a0), nullptr);
        *_write = _cell;
        _write = &std::get<typename mylist<T2>::Mycons>(_cell->v_mut()).d_a1;
        _loop_l = d_a1;
        continue;
      }
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
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<mylist<T1>> l = _f.l;
        if (std::holds_alternative<typename mylist<T1>::Mynil>(l->v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<T1>::Mycons>(l->v());
          _stack.emplace_back(_Call1{});
          _stack.emplace_back(_Enter{d_a1});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = (_result + 1);
      }
    }
    return _result;
  }
};

#endif // INCLUDED_DEEP_APP
