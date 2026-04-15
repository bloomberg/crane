#ifndef INCLUDED_DEEP_MAP
#define INCLUDED_DEEP_MAP

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

struct DeepMap {
  template <typename t_A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree<t_A>> d_a0;
      t_A d_a1;
      std::shared_ptr<tree<t_A>> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree<t_A>> leaf() {
      return std::make_shared<tree<t_A>>(Leaf{});
    }

    static std::shared_ptr<tree<t_A>>
    node(const std::shared_ptr<tree<t_A>> &a0, t_A a1,
         const std::shared_ptr<tree<t_A>> &a2) {
      return std::make_shared<tree<t_A>>(Node{a0, std::move(a1), a2});
    }

    static std::shared_ptr<tree<t_A>> node(std::shared_ptr<tree<t_A>> &&a0,
                                           t_A a1,
                                           std::shared_ptr<tree<t_A>> &&a2) {
      return std::make_shared<tree<t_A>>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, std::shared_ptr<tree<T1>>, T2, T1,
                   std::shared_ptr<tree<T1>>, T2>
                F1>
  static T2 tree_rect(const T2 f, F1 &&f0, const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s0;
      decltype(std::declval<typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T2 _s0;
      decltype(std::declval<typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<tree<T1>> t = _f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t->v())) {
          _result = f;
        } else {
          const auto &_m = *std::get_if<typename tree<T1>::Node>(&t->v());
          _stack.emplace_back(_Call1{_m.d_a0, _m.d_a2, _m.d_a1, _m.d_a0});
          _stack.emplace_back(_Enter{_m.d_a2});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        const auto &_f = std::get<_Call1>(_frame);
        _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
        _stack.emplace_back(_Enter{_f._s0});
      } else {
        const auto &_f = std::get<_Call2>(_frame);
        _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
      }
    }
    return _result;
  }

  template <typename T1, typename T2,
            MapsTo<T2, std::shared_ptr<tree<T1>>, T2, T1,
                   std::shared_ptr<tree<T1>>, T2>
                F1>
  static T2 tree_rec(const T2 f, F1 &&f0, const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s0;
      decltype(std::declval<typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T2 _s0;
      decltype(std::declval<typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<tree<T1>> t = _f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t->v())) {
          _result = f;
        } else {
          const auto &_m = *std::get_if<typename tree<T1>::Node>(&t->v());
          _stack.emplace_back(_Call1{_m.d_a0, _m.d_a2, _m.d_a1, _m.d_a0});
          _stack.emplace_back(_Enter{_m.d_a2});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        const auto &_f = std::get<_Call1>(_frame);
        _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
        _stack.emplace_back(_Enter{_f._s0});
      } else {
        const auto &_f = std::get<_Call2>(_frame);
        _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
      }
    }
    return _result;
  }

  /// Build a maximally-unbalanced tree (right spine = linked list).
  /// Tail-recursive via accumulator, should be loopified.
  static std::shared_ptr<tree<unsigned int>>
  build_right(const unsigned int n, std::shared_ptr<tree<unsigned int>> acc);

  /// Recursive tree map — visits every node.
  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<tree<T2>> tmap(F0 &&f,
                                        const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      decltype(std::declval<typename tree<T1>::Node &>().d_a0) _s0;
      T2 _s1;
    };

    struct _Call2 {
      std::shared_ptr<tree<T2>> _s0;
      T2 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    std::shared_ptr<tree<T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<tree<T1>> t = _f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t->v())) {
          _result = tree<T2>::leaf();
        } else {
          const auto &_m = *std::get_if<typename tree<T1>::Node>(&t->v());
          _stack.emplace_back(_Call1{_m.d_a0, f(_m.d_a1)});
          _stack.emplace_back(_Enter{_m.d_a2});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        const auto &_f = std::get<_Call1>(_frame);
        _stack.emplace_back(_Call2{_result, _f._s1});
        _stack.emplace_back(_Enter{_f._s0});
      } else {
        const auto &_f = std::get<_Call2>(_frame);
        _result = tree<T2>::node(_result, _f._s1, _f._s0);
      }
    }
    return _result;
  }

  static std::shared_ptr<tree<unsigned int>>
  map_inc(const std::shared_ptr<tree<unsigned int>> &t);

  /// Get root value.
  __attribute__((pure)) static unsigned int
  root_or_zero(const std::shared_ptr<tree<unsigned int>> &t);
};

#endif // INCLUDED_DEEP_MAP
