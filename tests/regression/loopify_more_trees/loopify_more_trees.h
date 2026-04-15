#ifndef INCLUDED_LOOPIFY_MORE_TREES
#define INCLUDED_LOOPIFY_MORE_TREES

#include <algorithm>
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

struct LoopifyMoreTrees {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> d_a0;
      unsigned int d_a1;
      std::shared_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree> leaf() {
      return std::make_shared<tree>(Leaf{});
    }

    static std::shared_ptr<tree> node(const std::shared_ptr<tree> &a0,
                                      unsigned int a1,
                                      const std::shared_ptr<tree> &a2) {
      return std::make_shared<tree>(Node{a0, std::move(a1), a2});
    }

    static std::shared_ptr<tree> node(std::shared_ptr<tree> &&a0,
                                      unsigned int a1,
                                      std::shared_ptr<tree> &&a2) {
      return std::make_shared<tree>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    struct _Enter {
      const std::shared_ptr<tree> t;
    };

    struct _Call1 {
      decltype(std::declval<typename tree::Node &>().d_a0) _s0;
      decltype(std::declval<typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<typename tree::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<typename tree::Node &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<tree> t = _f.t;
        if (std::holds_alternative<typename tree::Leaf>(t->v())) {
          _result = f;
        } else {
          const auto &_m = *std::get_if<typename tree::Node>(&t->v());
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

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    struct _Enter {
      const std::shared_ptr<tree> t;
    };

    struct _Call1 {
      decltype(std::declval<typename tree::Node &>().d_a0) _s0;
      decltype(std::declval<typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<typename tree::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<typename tree::Node &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<tree> t = _f.t;
        if (std::holds_alternative<typename tree::Leaf>(t->v())) {
          _result = f;
        } else {
          const auto &_m = *std::get_if<typename tree::Node>(&t->v());
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

  static std::shared_ptr<tree> mirror(const std::shared_ptr<tree> &t);
  __attribute__((pure)) static bool same_shape(const std::shared_ptr<tree> &t1,
                                               const std::shared_ptr<tree> &t2);
  static std::shared_ptr<List<unsigned int>>
  tree_to_list(const std::shared_ptr<tree> &t);
  __attribute__((pure)) static bool
  mirror_equal(const std::shared_ptr<tree> &t);
  __attribute__((pure)) static unsigned int
  count_nodes(const std::shared_ptr<tree> &t);
  static std::shared_ptr<tree> tree_max(std::shared_ptr<tree> t1,
                                        std::shared_ptr<tree> t2);
  __attribute__((pure)) static unsigned int
  sum_of_max_branches(const std::shared_ptr<tree> &t);
  static std::shared_ptr<tree> insert_bst(const unsigned int x,
                                          const std::shared_ptr<tree> &t);
  static std::shared_ptr<tree>
  build_bst(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  append_lists(const std::shared_ptr<List<unsigned int>> &l1,
               std::shared_ptr<List<unsigned int>> l2);
  static std::shared_ptr<List<unsigned int>>
  flatten(const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  map_tree_to_list(const std::shared_ptr<List<std::shared_ptr<tree>>> &lt);
  static std::shared_ptr<List<std::shared_ptr<tree>>>
  tree_children(const std::shared_ptr<tree> &t);
  static std::shared_ptr<List<std::shared_ptr<tree>>>
  append_trees(const std::shared_ptr<List<std::shared_ptr<tree>>> &l1,
               std::shared_ptr<List<std::shared_ptr<tree>>> l2);
  static std::shared_ptr<List<std::shared_ptr<tree>>>
  concat_map_children(const std::shared_ptr<List<std::shared_ptr<tree>>> &lt);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  tree_levels_fuel(const unsigned int fuel,
                   const std::shared_ptr<List<std::shared_ptr<tree>>> &level);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  tree_levels(std::shared_ptr<tree> t);
};

#endif // INCLUDED_LOOPIFY_MORE_TREES
