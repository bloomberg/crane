#ifndef INCLUDED_LOOPIFY_TREES
#define INCLUDED_LOOPIFY_TREES

#include <functional>
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
      std::visit(
          Overloaded{
              [&](const typename List<t_A>::Nil &) {
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = m;
                } else {
                  _head = m;
                }
                _continue = false;
              },
              [&](const typename List<t_A>::Cons &_args) {
                auto _cell = List<t_A>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 =
                      _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_self = _args.d_a1.get();
              }},
          _loop_self->v());
    }
    return _head;
  }
};

/// Consolidated UNIQUE tree algorithms - domain-specific tree operations.
struct LoopifyTrees {
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

    /// tree_map f t applies f to all values in tree.
    template <typename T1, MapsTo<T1, t_A> F0>
    std::shared_ptr<tree<T1>> tree_map(F0 &&f) const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename tree<t_A>::Node &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<F0 &>()(
            std::declval<const typename tree<t_A>::Node &>().d_a1)) _s1;
      };

      struct _Call2 {
        std::shared_ptr<tree<T1>> _s0;
        decltype(std::declval<F0 &>()(
            std::declval<const typename tree<t_A>::Node &>().d_a1)) _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      std::shared_ptr<tree<T1>> _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const tree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename tree<t_A>::Leaf &) -> void {
                            _result = tree<T1>::leaf();
                          },
                          [&](const typename tree<t_A>::Node &_args) -> void {
                            _stack.emplace_back(
                                _Call1{_args.d_a0.get(), f(_args.d_a1)});
                            _stack.emplace_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.emplace_back(_Call2{_result, _f._s1});
                  _stack.emplace_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = tree<T1>::node(_result, _f._s1, _f._s0);
                }},
            _frame);
      }
      return _result;
    }

    /// mirror_equal t1 t2 checks if t1 and t2 are mirror images.
    __attribute__((pure)) bool
    mirror_equal(const std::shared_ptr<tree<t_A>> &t2) const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
        const std::shared_ptr<tree<t_A>> t2;
      };

      struct _Call1 {
        decltype(std::declval<const typename tree<t_A>::Node &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename tree<t_A>::Node &>().d_a2) _s1;
        decltype(true) _s2;
      };

      struct _Call2 {
        bool _s0;
        decltype(true) _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      bool _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, t2});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const tree *_self = _f._self;
                  const std::shared_ptr<tree<t_A>> t2 = _f.t2;
                  std::visit(
                      Overloaded{
                          [&](const typename tree<t_A>::Leaf &) -> void {
                            _result = std::visit(
                                Overloaded{[](const typename tree<t_A>::Leaf &)
                                               -> bool { return true; },
                                           [](const typename tree<t_A>::Node &)
                                               -> bool { return false; }},
                                t2->v());
                          },
                          [&](const typename tree<t_A>::Node &_args) -> void {
                            std::visit(
                                Overloaded{
                                    [&](const typename tree<t_A>::Leaf &)
                                        -> void { _result = false; },
                                    [&](const typename tree<t_A>::Node &_args0)
                                        -> void {
                                      _stack.emplace_back(_Call1{
                                          _args.d_a0.get(), _args0.d_a2, true});
                                      _stack.emplace_back(_Enter{
                                          _args.d_a2.get(), _args0.d_a0});
                                    }},
                                t2->v());
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.emplace_back(_Call2{_result, _f._s2});
                  _stack.emplace_back(_Enter{_f._s0, _f._s1});
                },
                [&](_Call2 _f) { _result = ((_result && _f._s0) && _f._s1); }},
            _frame);
      }
      return _result;
    }

    /// tree_to_list inorder traversal.
    std::shared_ptr<List<t_A>> tree_to_list() const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename tree<t_A>::Node &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename tree<t_A>::Node &>().d_a1) _s1;
      };

      struct _Call2 {
        std::shared_ptr<List<t_A>> _s0;
        decltype(std::declval<const typename tree<t_A>::Node &>().d_a1) _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      std::shared_ptr<List<t_A>> _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const tree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename tree<t_A>::Leaf &) -> void {
                            _result = List<t_A>::nil();
                          },
                          [&](const typename tree<t_A>::Node &_args) -> void {
                            _stack.emplace_back(
                                _Call1{_args.d_a0.get(), _args.d_a1});
                            _stack.emplace_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.emplace_back(_Call2{_result, _f._s1});
                  _stack.emplace_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = _result->app(List<t_A>::cons(_f._s1, _f._s0));
                }},
            _frame);
      }
      return _result;
    }

    /// count_leaves counts leaf nodes.
    __attribute__((pure)) unsigned int count_leaves() const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename tree<t_A>::Node &>()
                     .d_a0.get()) _s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const tree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename tree<t_A>::Leaf &) -> void {
                            _result = 1u;
                          },
                          [&](const typename tree<t_A>::Node &_args) -> void {
                            _stack.emplace_back(_Call1{_args.d_a0.get()});
                            _stack.emplace_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.emplace_back(_Call2{_result});
                  _stack.emplace_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) { _result = (_result + _f._s0); }},
            _frame);
      }
      return _result;
    }

    /// same_shape tests structural equality.
    template <typename T1>
    __attribute__((pure)) bool
    same_shape(const std::shared_ptr<tree<T1>> &t2) const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
        const std::shared_ptr<tree<T1>> t2;
      };

      struct _Call1 {
        const typename tree<T1>::Node _s0;
        const typename tree<t_A>::Node _s1;
      };

      using _Frame = std::variant<_Enter, _Call1>;
      bool _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, t2});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const tree *_self = _f._self;
                  const std::shared_ptr<tree<T1>> t2 = _f.t2;
                  std::visit(
                      Overloaded{
                          [&](const typename tree<t_A>::Leaf &) -> void {
                            _result = std::visit(
                                Overloaded{[](const typename tree<T1>::Leaf &)
                                               -> bool { return true; },
                                           [](const typename tree<T1>::Node &)
                                               -> bool { return false; }},
                                t2->v());
                          },
                          [&](const typename tree<t_A>::Node &_args) -> void {
                            std::visit(
                                Overloaded{
                                    [&](const typename tree<T1>::Leaf &)
                                        -> void { _result = false; },
                                    [&](const typename tree<T1>::Node &_args0)
                                        -> void {
                                      _stack.emplace_back(
                                          _Call1{_args0, _args});
                                      _stack.emplace_back(_Enter{
                                          _args.d_a0.get(), _args0.d_a0});
                                    }},
                                t2->v());
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  const typename tree<T1>::Node _args0 = _f._s0;
                  const typename tree<t_A>::Node _args = _f._s1;
                  if (_result) {
                    _stack.emplace_back(_Enter{_args.d_a2.get(), _args0.d_a2});
                  } else {
                    _result = false;
                  }
                }},
            _frame);
      }
      return _result;
    }

    std::shared_ptr<tree<t_A>> mirror() const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename tree<t_A>::Node &>()
                     .d_a2.get()) _s0;
        decltype(std::declval<const typename tree<t_A>::Node &>().d_a1) _s1;
      };

      struct _Call2 {
        std::shared_ptr<tree<t_A>> _s0;
        decltype(std::declval<const typename tree<t_A>::Node &>().d_a1) _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      std::shared_ptr<tree<t_A>> _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const tree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename tree<t_A>::Leaf &) -> void {
                            _result = tree<t_A>::leaf();
                          },
                          [&](const typename tree<t_A>::Node &_args) -> void {
                            _stack.emplace_back(
                                _Call1{_args.d_a2.get(), _args.d_a1});
                            _stack.emplace_back(_Enter{_args.d_a0.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.emplace_back(_Call2{_result, _f._s1});
                  _stack.emplace_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = tree<t_A>::node(_result, _f._s1, _f._s0);
                }},
            _frame);
      }
      return _result;
    }

    __attribute__((pure)) unsigned int tree_size() const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename tree<t_A>::Node &>()
                     .d_a0.get()) _s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const tree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename tree<t_A>::Leaf &) -> void {
                            _result = 0u;
                          },
                          [&](const typename tree<t_A>::Node &_args) -> void {
                            _stack.emplace_back(_Call1{_args.d_a0.get()});
                            _stack.emplace_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.emplace_back(_Call2{_result});
                  _stack.emplace_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) { _result = ((_result + _f._s0) + 1); }},
            _frame);
      }
      return _result;
    }

    __attribute__((pure)) unsigned int tree_height() const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        const typename tree<t_A>::Node _s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const tree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename tree<t_A>::Leaf &) -> void {
                            _result = 0u;
                          },
                          [&](const typename tree<t_A>::Node &_args) -> void {
                            _stack.emplace_back(_Call1{_args});
                            _stack.emplace_back(_Enter{_args.d_a0.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  const typename tree<t_A>::Node _args = _f._s0;
                  unsigned int lh = _result;
                  _stack.emplace_back(_Call2{lh});
                  _stack.emplace_back(_Enter{_args.d_a2.get()});
                },
                [&](_Call2 _f) {
                  unsigned int lh = _f._s0;
                  unsigned int rh = _result;
                  _result = ([&]() -> unsigned int {
                    if (lh <= rh) {
                      return rh;
                    } else {
                      return lh;
                    }
                  }() + 1);
                }},
            _frame);
      }
      return _result;
    }
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
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s0;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T2 _s0;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<tree<T1>> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename tree<T1>::Leaf &) -> void {
                          _result = f;
                        },
                        [&](const typename tree<T1>::Node &_args) -> void {
                          _stack.emplace_back(_Call1{_args.d_a0, _args.d_a2,
                                                     _args.d_a1, _args.d_a0});
                          _stack.emplace_back(_Enter{_args.d_a2});
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
                _stack.emplace_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
              }},
          _frame);
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
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s0;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T2 _s0;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree<T1>::Node &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<tree<T1>> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename tree<T1>::Leaf &) -> void {
                          _result = f;
                        },
                        [&](const typename tree<T1>::Node &_args) -> void {
                          _stack.emplace_back(_Call1{_args.d_a0, _args.d_a2,
                                                     _args.d_a1, _args.d_a0});
                          _stack.emplace_back(_Enter{_args.d_a2});
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
                _stack.emplace_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  __attribute__((pure)) static unsigned int
  tree_sum(const std::shared_ptr<tree<unsigned int>> &t);

  /// leftmost/rightmost finds edge values.
  template <typename T1>
  static T1 leftmost(const T1 default0, const std::shared_ptr<tree<T1>> &t) {
    T1 _result;
    std::shared_ptr<tree<T1>> _loop_t = t;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{[&](const typename tree<T1>::Leaf &) {
                       _result = default0;
                       _continue = false;
                     },
                     [&](const typename tree<T1>::Node &_args) {
                       std::visit(
                           Overloaded{[&](const typename tree<T1>::Leaf &) {
                                        _result = _args.d_a1;
                                        _continue = false;
                                      },
                                      [&](const typename tree<T1>::Node &) {
                                        _loop_t = _args.d_a0;
                                      }},
                           _args.d_a0->v());
                     }},
          _loop_t->v());
    }
    return _result;
  }

  template <typename T1>
  static T1 rightmost(const T1 default0, const std::shared_ptr<tree<T1>> &t) {
    T1 _result;
    std::shared_ptr<tree<T1>> _loop_t = t;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{[&](const typename tree<T1>::Leaf &) {
                       _result = default0;
                       _continue = false;
                     },
                     [&](const typename tree<T1>::Node &_args) {
                       std::visit(
                           Overloaded{[&](const typename tree<T1>::Leaf &) {
                                        _result = _args.d_a1;
                                        _continue = false;
                                      },
                                      [&](const typename tree<T1>::Node &) {
                                        _loop_t = _args.d_a2;
                                      }},
                           _args.d_a2->v());
                     }},
          _loop_t->v());
    }
    return _result;
  }

  /// leaf_sum sums only leaf values.
  __attribute__((pure)) static unsigned int
  leaf_sum(const std::shared_ptr<tree<unsigned int>> &t);
  /// insert_bst BST insertion.
  static std::shared_ptr<tree<unsigned int>>
  insert_bst(const unsigned int x,
             const std::shared_ptr<tree<unsigned int>> &t);
  /// count_paths t n counts root-to-leaf paths that sum to n.
  __attribute__((pure)) static unsigned int
  count_paths(const std::shared_ptr<tree<unsigned int>> &t,
              const unsigned int n);
  /// sum_of_max_branches sums maximum values along each path.
  __attribute__((pure)) static unsigned int
  sum_of_max_branches(const std::shared_ptr<tree<unsigned int>> &t);

  struct ternary {
    // TYPES
    struct TLeaf {};

    struct TNode {
      std::shared_ptr<ternary> d_a0;
      std::shared_ptr<ternary> d_a1;
      std::shared_ptr<ternary> d_a2;
      unsigned int d_a3;
    };

    using variant_t = std::variant<TLeaf, TNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit ternary(TLeaf _v) : d_v_(_v) {}

    explicit ternary(TNode _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<ternary> tleaf() {
      return std::make_shared<ternary>(TLeaf{});
    }

    static std::shared_ptr<ternary> tnode(const std::shared_ptr<ternary> &a0,
                                          const std::shared_ptr<ternary> &a1,
                                          const std::shared_ptr<ternary> &a2,
                                          unsigned int a3) {
      return std::make_shared<ternary>(TNode{a0, a1, a2, std::move(a3)});
    }

    static std::shared_ptr<ternary> tnode(std::shared_ptr<ternary> &&a0,
                                          std::shared_ptr<ternary> &&a1,
                                          std::shared_ptr<ternary> &&a2,
                                          unsigned int a3) {
      return std::make_shared<ternary>(
          TNode{std::move(a0), std::move(a1), std::move(a2), std::move(a3)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int ternary_depth() const {
      const ternary *_self = this;

      struct _Enter {
        const ternary *_self;
      };

      struct _Call1 {
        const typename ternary::TNode _s0;
      };

      struct _Call2 {
        const typename ternary::TNode _s0;
        unsigned int _s1;
      };

      struct _Call3 {
        unsigned int _s0;
        unsigned int _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const ternary *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename ternary::TLeaf &) -> void {
                            _result = 0u;
                          },
                          [&](const typename ternary::TNode &_args) -> void {
                            _stack.emplace_back(_Call1{_args});
                            _stack.emplace_back(_Enter{_args.d_a0.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  const typename ternary::TNode _args = _f._s0;
                  unsigned int d1 = _result;
                  _stack.emplace_back(_Call2{_args, d1});
                  _stack.emplace_back(_Enter{_args.d_a1.get()});
                },
                [&](_Call2 _f) {
                  const typename ternary::TNode _args = _f._s0;
                  unsigned int d1 = _f._s1;
                  unsigned int d2 = _result;
                  _stack.emplace_back(_Call3{d1, d2});
                  _stack.emplace_back(_Enter{_args.d_a2.get()});
                },
                [&](_Call3 _f) {
                  unsigned int d1 = _f._s0;
                  unsigned int d2 = _f._s1;
                  unsigned int d3 = _result;
                  _result = ([&]() -> unsigned int {
                    if ([&]() -> unsigned int {
                          if (d1 <= d2) {
                            return d2;
                          } else {
                            return d1;
                          }
                        }() <= d3) {
                      return d3;
                    } else {
                      if (d1 <= d2) {
                        return d2;
                      } else {
                        return d1;
                      }
                    }
                  }() + 1);
                }},
            _frame);
      }
      return _result;
    }

    __attribute__((pure)) unsigned int ternary_sum() const {
      const ternary *_self = this;

      struct _Enter {
        const ternary *_self;
      };

      struct _Call1 {
        const ternary *_s0;
        const ternary *_s1;
        decltype(std::declval<const typename ternary::TNode &>().d_a3) _s2;
      };

      struct _Call2 {
        unsigned int _s0;
        const ternary *_s1;
        decltype(std::declval<const typename ternary::TNode &>().d_a3) _s2;
      };

      struct _Call3 {
        unsigned int _s0;
        unsigned int _s1;
        decltype(std::declval<const typename ternary::TNode &>().d_a3) _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const ternary *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename ternary::TLeaf &) -> void {
                            _result = 0u;
                          },
                          [&](const typename ternary::TNode &_args) -> void {
                            _stack.emplace_back(_Call1{_args.d_a1.get(),
                                                       _args.d_a0.get(),
                                                       _args.d_a3});
                            _stack.emplace_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.emplace_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _stack.emplace_back(_Call3{_f._s0, _result, _f._s2});
                  _stack.emplace_back(_Enter{_f._s1});
                },
                [&](_Call3 _f) {
                  _result = (_f._s2 + (_result + (_f._s1 + _f._s0)));
                }},
            _frame);
      }
      return _result;
    }
  };

  template <typename T1,
            MapsTo<T1, std::shared_ptr<ternary>, T1, std::shared_ptr<ternary>,
                   T1, std::shared_ptr<ternary>, T1, unsigned int>
                F1>
  static T1 ternary_rect(const T1 f, F1 &&f0,
                         const std::shared_ptr<ternary> &t) {
    struct _Enter {
      const std::shared_ptr<ternary> t;
    };

    struct _Call1 {
      const std::shared_ptr<ternary> _s0;
      const std::shared_ptr<ternary> _s1;
      decltype(std::declval<const typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<const typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<const typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<const typename ternary::TNode &>().d_a0) _s5;
    };

    struct _Call2 {
      T1 _s0;
      const std::shared_ptr<ternary> _s1;
      decltype(std::declval<const typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<const typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<const typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<const typename ternary::TNode &>().d_a0) _s5;
    };

    struct _Call3 {
      T1 _s0;
      T1 _s1;
      decltype(std::declval<const typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<const typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<const typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<const typename ternary::TNode &>().d_a0) _s5;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<ternary> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename ternary::TLeaf &) -> void {
                          _result = f;
                        },
                        [&](const typename ternary::TNode &_args) -> void {
                          _stack.emplace_back(_Call1{_args.d_a1, _args.d_a0,
                                                     _args.d_a3, _args.d_a2,
                                                     _args.d_a1, _args.d_a0});
                          _stack.emplace_back(_Enter{_args.d_a2});
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.emplace_back(
                    _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5});
                _stack.emplace_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _stack.emplace_back(
                    _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5});
                _stack.emplace_back(_Enter{_f._s1});
              },
              [&](_Call3 _f) {
                _result =
                    f0(_f._s5, _result, _f._s4, _f._s1, _f._s3, _f._s0, _f._s2);
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1,
            MapsTo<T1, std::shared_ptr<ternary>, T1, std::shared_ptr<ternary>,
                   T1, std::shared_ptr<ternary>, T1, unsigned int>
                F1>
  static T1 ternary_rec(const T1 f, F1 &&f0,
                        const std::shared_ptr<ternary> &t) {
    struct _Enter {
      const std::shared_ptr<ternary> t;
    };

    struct _Call1 {
      const std::shared_ptr<ternary> _s0;
      const std::shared_ptr<ternary> _s1;
      decltype(std::declval<const typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<const typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<const typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<const typename ternary::TNode &>().d_a0) _s5;
    };

    struct _Call2 {
      T1 _s0;
      const std::shared_ptr<ternary> _s1;
      decltype(std::declval<const typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<const typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<const typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<const typename ternary::TNode &>().d_a0) _s5;
    };

    struct _Call3 {
      T1 _s0;
      T1 _s1;
      decltype(std::declval<const typename ternary::TNode &>().d_a3) _s2;
      decltype(std::declval<const typename ternary::TNode &>().d_a2) _s3;
      decltype(std::declval<const typename ternary::TNode &>().d_a1) _s4;
      decltype(std::declval<const typename ternary::TNode &>().d_a0) _s5;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<ternary> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename ternary::TLeaf &) -> void {
                          _result = f;
                        },
                        [&](const typename ternary::TNode &_args) -> void {
                          _stack.emplace_back(_Call1{_args.d_a1, _args.d_a0,
                                                     _args.d_a3, _args.d_a2,
                                                     _args.d_a1, _args.d_a0});
                          _stack.emplace_back(_Enter{_args.d_a2});
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.emplace_back(
                    _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5});
                _stack.emplace_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _stack.emplace_back(
                    _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5});
                _stack.emplace_back(_Enter{_f._s1});
              },
              [&](_Call3 _f) {
                _result =
                    f0(_f._s5, _result, _f._s4, _f._s1, _f._s3, _f._s0, _f._s2);
              }},
          _frame);
    }
    return _result;
  }

  /// Rose tree: a tree with variable number of children.
  struct rose {
    // TYPES
    struct RNode {
      unsigned int d_a0;
      std::shared_ptr<List<std::shared_ptr<rose>>> d_a1;
    };

    using variant_t = std::variant<RNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit rose(RNode _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<rose>
    rnode(unsigned int a0,
          const std::shared_ptr<List<std::shared_ptr<rose>>> &a1) {
      return std::make_shared<rose>(RNode{std::move(a0), a1});
    }

    static std::shared_ptr<rose>
    rnode(unsigned int a0, std::shared_ptr<List<std::shared_ptr<rose>>> &&a1) {
      return std::make_shared<rose>(RNode{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// rose_depth t computes the depth of a rose tree.
    __attribute__((pure)) unsigned int rose_depth() const {
      return std::visit(
          Overloaded{[](const typename rose::RNode &_args) -> unsigned int {
            return (depth_rose_list_fuel(1000u, _args.d_a1) + 1);
          }},
          this->v());
    }

    /// rose_flatten t flattens a rose tree to a list (pre-order).
    std::shared_ptr<List<unsigned int>> rose_flatten() const {
      return std::visit(Overloaded{[](const typename rose::RNode &_args)
                                       -> std::shared_ptr<List<unsigned int>> {
                          return List<unsigned int>::cons(
                              _args.d_a0,
                              flatten_rose_list_fuel(1000u, _args.d_a1));
                        }},
                        this->v());
    }

    /// rose_map f t applies f to all values in a rose tree.
    template <MapsTo<unsigned int, unsigned int> F0>
    std::shared_ptr<rose> rose_map(F0 &&f) const {
      return std::visit(
          Overloaded{
              [&](const typename rose::RNode &_args) -> std::shared_ptr<rose> {
                return rose::rnode(f(_args.d_a0),
                                   map_rose_list_fuel(1000u, f, _args.d_a1));
              }},
          this->v());
    }

    /// rose_sum t sums all values in a rose tree.
    __attribute__((pure)) unsigned int rose_sum() const {
      return std::visit(
          Overloaded{[](const typename rose::RNode &_args) -> unsigned int {
            return (_args.d_a0 + sum_rose_list_fuel(1000u, _args.d_a1));
          }},
          this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int,
                                  std::shared_ptr<List<std::shared_ptr<rose>>>>
                               F0>
    T1 rose_rec(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename rose::RNode &_args) -> T1 {
            return f(_args.d_a0, _args.d_a1);
          }},
          this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int,
                                  std::shared_ptr<List<std::shared_ptr<rose>>>>
                               F0>
    T1 rose_rect(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename rose::RNode &_args) -> T1 {
            return f(_args.d_a0, _args.d_a1);
          }},
          this->v());
    }
  };

  /// Helper: sum all values in a list of rose trees (processes both tree and
  /// list levels in one recursive function to enable full loopification).
  __attribute__((pure)) static unsigned int
  sum_rose_list_fuel(const unsigned int fuel,
                     const std::shared_ptr<List<std::shared_ptr<rose>>> &cs);

  /// Helper: map function over all values in a list of rose trees.
  template <MapsTo<unsigned int, unsigned int> F1>
  static std::shared_ptr<List<std::shared_ptr<rose>>>
  map_rose_list_fuel(const unsigned int fuel, F1 &&f,
                     const std::shared_ptr<List<std::shared_ptr<rose>>> &cs) {
    struct _Enter {
      const std::shared_ptr<List<std::shared_ptr<rose>>> cs;
      const unsigned int fuel;
    };

    struct _Call1 {
      decltype(std::declval<const typename rose::RNode &>().d_a1) _s0;
      unsigned int _s1;
      unsigned int _s2;
    };

    struct _Call2 {
      std::shared_ptr<List<std::shared_ptr<rose>>> _s0;
      unsigned int _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    std::shared_ptr<List<std::shared_ptr<rose>>> _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{cs, fuel});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<std::shared_ptr<rose>>> cs = _f.cs;
                const unsigned int fuel = _f.fuel;
                if (fuel <= 0) {
                  _result = List<std::shared_ptr<rose>>::nil();
                } else {
                  unsigned int g = fuel - 1;
                  std::visit(
                      Overloaded{
                          [&](const typename List<std::shared_ptr<rose>>::Nil &)
                              -> void {
                            _result = List<std::shared_ptr<rose>>::nil();
                          },
                          [&](const typename List<std::shared_ptr<rose>>::Cons
                                  &_args) -> void {
                            std::visit(
                                Overloaded{[&](const typename rose::RNode
                                                   &_args0) -> void {
                                  _stack.emplace_back(
                                      _Call1{_args0.d_a1, g, f(_args0.d_a0)});
                                  _stack.emplace_back(_Enter{_args.d_a1, g});
                                }},
                                _args.d_a0->v());
                          }},
                      cs->v());
                }
              },
              [&](_Call1 _f) {
                _stack.emplace_back(_Call2{_result, _f._s2});
                _stack.emplace_back(_Enter{_f._s0, _f._s1});
              },
              [&](_Call2 _f) {
                _result = List<std::shared_ptr<rose>>::cons(
                    rose::rnode(_f._s1, _result), _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  /// Helper: flatten a list of rose trees to a flat list of nats.
  static std::shared_ptr<List<unsigned int>> flatten_rose_list_fuel(
      const unsigned int fuel,
      const std::shared_ptr<List<std::shared_ptr<rose>>> &cs);
  /// Helper: compute maximum depth among a list of rose trees.
  __attribute__((pure)) static unsigned int
  depth_rose_list_fuel(const unsigned int fuel,
                       const std::shared_ptr<List<std::shared_ptr<rose>>> &cs);
  /// tree_max t1 t2 element-wise maximum of two trees.
  static std::shared_ptr<tree<unsigned int>>
  tree_max(std::shared_ptr<tree<unsigned int>> t1,
           std::shared_ptr<tree<unsigned int>> t2);
  /// Helper: extract values from trees.
  static std::shared_ptr<List<unsigned int>> extract_tree_values(
      const std::shared_ptr<List<std::shared_ptr<tree<unsigned int>>>> &ts);
  /// Helper: extract children from trees.
  static std::shared_ptr<List<std::shared_ptr<tree<unsigned int>>>>
  extract_tree_children(
      const std::shared_ptr<List<std::shared_ptr<tree<unsigned int>>>> &ts);
  /// tree_levels t returns list of lists, one per level (breadth-first).
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  tree_levels_fuel(
      const unsigned int fuel,
      const std::shared_ptr<List<std::shared_ptr<tree<unsigned int>>>> &trees);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  tree_levels(std::shared_ptr<tree<unsigned int>> t);
  /// count_nodes t returns tuple (node_count, sum_of_values).
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  count_nodes(const std::shared_ptr<tree<unsigned int>> &t);
  /// Helper: append two lists of lists.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  append_list_lists(
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &l1,
      std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> l2);
  /// Helper: prepend value to all lists in a list of lists.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  map_cons_to_all(
      const unsigned int x,
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &lsts);
  /// paths t returns all root-to-leaf paths in tree.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  paths(const std::shared_ptr<tree<unsigned int>> &t);
  /// collect_sorted t collects and sorts all tree values.
  static std::shared_ptr<List<unsigned int>>
  collect_unsorted(const std::shared_ptr<tree<unsigned int>> &t);
  /// Simple insertion sort for collect_sorted.
  static std::shared_ptr<List<unsigned int>>
  insert_sorted(const unsigned int x,
                const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  sort_list(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>> collect_sorted(
      const std::shared_ptr<tree<unsigned int>>
          &t); /// or_search p t searches tree for element satisfying predicate.

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool
  or_search(F0 &&p, const std::shared_ptr<tree<unsigned int>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<unsigned int>> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename tree<unsigned int>::Node &>()
                   .d_a0) _s0;
    };

    struct _Call2 {
      bool _s0;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<tree<unsigned int>> t = _f.t;
                std::visit(
                    Overloaded{
                        [&](const typename tree<unsigned int>::Leaf &) -> void {
                          _result = false;
                        },
                        [&](const typename tree<unsigned int>::Node &_args)
                            -> void {
                          if (p(_args.d_a1)) {
                            _result = true;
                          } else {
                            _stack.emplace_back(_Call1{_args.d_a0});
                            _stack.emplace_back(_Enter{_args.d_a2});
                          }
                        }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.emplace_back(_Call2{_result});
                _stack.emplace_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) { _result = (_result || _f._s0); }},
          _frame);
    }
    return _result;
  }

  struct quadtree {
    // TYPES
    struct QLeaf {
      unsigned int d_a0;
    };

    struct Quad {
      std::shared_ptr<quadtree> d_a0;
      std::shared_ptr<quadtree> d_a1;
      std::shared_ptr<quadtree> d_a2;
      std::shared_ptr<quadtree> d_a3;
    };

    using variant_t = std::variant<QLeaf, Quad>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit quadtree(QLeaf _v) : d_v_(std::move(_v)) {}

    explicit quadtree(Quad _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<quadtree> qleaf(unsigned int a0) {
      return std::make_shared<quadtree>(QLeaf{std::move(a0)});
    }

    static std::shared_ptr<quadtree> quad(const std::shared_ptr<quadtree> &a0,
                                          const std::shared_ptr<quadtree> &a1,
                                          const std::shared_ptr<quadtree> &a2,
                                          const std::shared_ptr<quadtree> &a3) {
      return std::make_shared<quadtree>(Quad{a0, a1, a2, a3});
    }

    static std::shared_ptr<quadtree> quad(std::shared_ptr<quadtree> &&a0,
                                          std::shared_ptr<quadtree> &&a1,
                                          std::shared_ptr<quadtree> &&a2,
                                          std::shared_ptr<quadtree> &&a3) {
      return std::make_shared<quadtree>(
          Quad{std::move(a0), std::move(a1), std::move(a2), std::move(a3)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// quad_depth t computes depth of quadtree.
    __attribute__((pure)) unsigned int quad_depth() const {
      const quadtree *_self = this;

      struct _Enter {
        const quadtree *_self;
      };

      struct _Call1 {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      struct _Call2 {
        unsigned int _s0;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      struct _Call3 {
        unsigned int _s0;
        unsigned int _s1;
        const quadtree *_s2;
      };

      struct _Call4 {
        unsigned int _s0;
        unsigned int _s1;
        unsigned int _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const quadtree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename quadtree::QLeaf &) -> void {
                            _result = 0u;
                          },
                          [&](const typename quadtree::Quad &_args) -> void {
                            _stack.emplace_back(_Call1{_args.d_a2.get(),
                                                       _args.d_a1.get(),
                                                       _args.d_a0.get()});
                            _stack.emplace_back(_Enter{_args.d_a3.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.emplace_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _stack.emplace_back(_Call3{_f._s0, _result, _f._s2});
                  _stack.emplace_back(_Enter{_f._s1});
                },
                [&](_Call3 _f) {
                  _stack.emplace_back(_Call4{_f._s0, _f._s1, _result});
                  _stack.emplace_back(_Enter{_f._s2});
                },
                [&](_Call4 _f) {
                  _result = (max4_impl(_result, _f._s2, _f._s1, _f._s0) + 1);
                }},
            _frame);
      }
      return _result;
    }

    /// quad_sum t sums all values in a quadtree.
    __attribute__((pure)) unsigned int quad_sum() const {
      const quadtree *_self = this;

      struct _Enter {
        const quadtree *_self;
      };

      struct _Call1 {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      struct _Call2 {
        unsigned int _s0;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      struct _Call3 {
        unsigned int _s0;
        unsigned int _s1;
        const quadtree *_s2;
      };

      struct _Call4 {
        unsigned int _s0;
        unsigned int _s1;
        unsigned int _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const quadtree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename quadtree::QLeaf &_args) -> void {
                            _result = _args.d_a0;
                          },
                          [&](const typename quadtree::Quad &_args) -> void {
                            _stack.emplace_back(_Call1{_args.d_a2.get(),
                                                       _args.d_a1.get(),
                                                       _args.d_a0.get()});
                            _stack.emplace_back(_Enter{_args.d_a3.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.emplace_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _stack.emplace_back(_Call3{_f._s0, _result, _f._s2});
                  _stack.emplace_back(_Enter{_f._s1});
                },
                [&](_Call3 _f) {
                  _stack.emplace_back(_Call4{_f._s0, _f._s1, _result});
                  _stack.emplace_back(_Enter{_f._s2});
                },
                [&](_Call4 _f) {
                  _result = (_result + (_f._s2 + (_f._s1 + _f._s0)));
                }},
            _frame);
      }
      return _result;
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, std::shared_ptr<quadtree>, T1, std::shared_ptr<quadtree>, T1,
               std::shared_ptr<quadtree>, T1, std::shared_ptr<quadtree>, T1>
            F1>
    T1 quadtree_rec(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      struct _Enter {
        const quadtree *_self;
      };

      struct _Call1 {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
        decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
        decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
        decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
        decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
      };

      struct _Call2 {
        T1 _s0;
        const quadtree *_s1;
        const quadtree *_s2;
        decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
        decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
        decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
        decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
      };

      struct _Call3 {
        T1 _s0;
        T1 _s1;
        const quadtree *_s2;
        decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
        decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
        decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
        decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
      };

      struct _Call4 {
        T1 _s0;
        T1 _s1;
        T1 _s2;
        decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
        decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
        decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
        decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const quadtree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename quadtree::QLeaf &_args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename quadtree::Quad &_args) -> void {
                            _stack.emplace_back(
                                _Call1{_args.d_a2.get(), _args.d_a1.get(),
                                       _args.d_a0.get(), _args.d_a3, _args.d_a2,
                                       _args.d_a1, _args.d_a0});
                            _stack.emplace_back(_Enter{_args.d_a3.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3,
                                             _f._s4, _f._s5, _f._s6});
                  _stack.emplace_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _stack.emplace_back(_Call3{_f._s0, _result, _f._s2, _f._s3,
                                             _f._s4, _f._s5, _f._s6});
                  _stack.emplace_back(_Enter{_f._s1});
                },
                [&](_Call3 _f) {
                  _stack.emplace_back(_Call4{_f._s0, _f._s1, _result, _f._s3,
                                             _f._s4, _f._s5, _f._s6});
                  _stack.emplace_back(_Enter{_f._s2});
                },
                [&](_Call4 _f) {
                  _result = f0(_f._s6, _result, _f._s5, _f._s2, _f._s4, _f._s1,
                               _f._s3, _f._s0);
                }},
            _frame);
      }
      return _result;
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, std::shared_ptr<quadtree>, T1, std::shared_ptr<quadtree>, T1,
               std::shared_ptr<quadtree>, T1, std::shared_ptr<quadtree>, T1>
            F1>
    T1 quadtree_rect(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      struct _Enter {
        const quadtree *_self;
      };

      struct _Call1 {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
        decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
        decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
        decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
        decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
      };

      struct _Call2 {
        T1 _s0;
        const quadtree *_s1;
        const quadtree *_s2;
        decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
        decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
        decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
        decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
      };

      struct _Call3 {
        T1 _s0;
        T1 _s1;
        const quadtree *_s2;
        decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
        decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
        decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
        decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
      };

      struct _Call4 {
        T1 _s0;
        T1 _s1;
        T1 _s2;
        decltype(std::declval<const typename quadtree::Quad &>().d_a3) _s3;
        decltype(std::declval<const typename quadtree::Quad &>().d_a2) _s4;
        decltype(std::declval<const typename quadtree::Quad &>().d_a1) _s5;
        decltype(std::declval<const typename quadtree::Quad &>().d_a0) _s6;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const quadtree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename quadtree::QLeaf &_args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename quadtree::Quad &_args) -> void {
                            _stack.emplace_back(
                                _Call1{_args.d_a2.get(), _args.d_a1.get(),
                                       _args.d_a0.get(), _args.d_a3, _args.d_a2,
                                       _args.d_a1, _args.d_a0});
                            _stack.emplace_back(_Enter{_args.d_a3.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3,
                                             _f._s4, _f._s5, _f._s6});
                  _stack.emplace_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _stack.emplace_back(_Call3{_f._s0, _result, _f._s2, _f._s3,
                                             _f._s4, _f._s5, _f._s6});
                  _stack.emplace_back(_Enter{_f._s1});
                },
                [&](_Call3 _f) {
                  _stack.emplace_back(_Call4{_f._s0, _f._s1, _result, _f._s3,
                                             _f._s4, _f._s5, _f._s6});
                  _stack.emplace_back(_Enter{_f._s2});
                },
                [&](_Call4 _f) {
                  _result = f0(_f._s6, _result, _f._s5, _f._s2, _f._s4, _f._s1,
                               _f._s3, _f._s0);
                }},
            _frame);
      }
      return _result;
    }
  };

  /// Helper: max of 4 values using nested max.
  __attribute__((pure)) static unsigned int max4_impl(const unsigned int a,
                                                      const unsigned int b,
                                                      const unsigned int c,
                                                      const unsigned int d);

  /// Simple binary tree with values only at leaves.
  struct simple_tree {
    // TYPES
    struct SLeaf {
      unsigned int d_a0;
    };

    struct SNode {
      std::shared_ptr<simple_tree> d_a0;
      std::shared_ptr<simple_tree> d_a1;
    };

    using variant_t = std::variant<SLeaf, SNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit simple_tree(SLeaf _v) : d_v_(std::move(_v)) {}

    explicit simple_tree(SNode _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<simple_tree> sleaf(unsigned int a0) {
      return std::make_shared<simple_tree>(SLeaf{std::move(a0)});
    }

    static std::shared_ptr<simple_tree>
    snode(const std::shared_ptr<simple_tree> &a0,
          const std::shared_ptr<simple_tree> &a1) {
      return std::make_shared<simple_tree>(SNode{a0, a1});
    }

    static std::shared_ptr<simple_tree>
    snode(std::shared_ptr<simple_tree> &&a0,
          std::shared_ptr<simple_tree> &&a1) {
      return std::make_shared<simple_tree>(SNode{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// count_paths_simple t n counts paths with sum n (simpler variant).
    __attribute__((pure)) unsigned int
    count_paths_simple(const unsigned int n) const {
      const simple_tree *_self = this;

      struct _Enter {
        const simple_tree *_self;
        const unsigned int n;
      };

      struct _Call1 {
        decltype(std::declval<const typename simple_tree::SNode &>()
                     .d_a0.get()) _s0;
        decltype((((std::declval<const unsigned int &>() - 1u) >
                           std::declval<const unsigned int &>()
                       ? 0
                       : (std::declval<const unsigned int &>() - 1u)))) _s1;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, n});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{[&](_Enter _f) {
                         const simple_tree *_self = _f._self;
                         const unsigned int n = _f.n;
                         std::visit(
                             Overloaded{
                                 [&](const typename simple_tree::SLeaf &_args)
                                     -> void {
                                   if (_args.d_a0 == n) {
                                     _result = 1u;
                                   } else {
                                     _result = 0u;
                                   }
                                 },
                                 [&](const typename simple_tree::SNode &_args)
                                     -> void {
                                   if (n <= 0u) {
                                     _result = 0u;
                                   } else {
                                     _stack.emplace_back(_Call1{
                                         _args.d_a0.get(),
                                         (((n - 1u) > n ? 0 : (n - 1u)))});
                                     _stack.emplace_back(_Enter{
                                         _args.d_a1.get(),
                                         (((n - 1u) > n ? 0 : (n - 1u)))});
                                   }
                                 }},
                             _self->v());
                       },
                       [&](_Call1 _f) {
                         _stack.emplace_back(_Call2{_result});
                         _stack.emplace_back(_Enter{_f._s0, _f._s1});
                       },
                       [&](_Call2 _f) { _result = (_result + _f._s0); }},
            _frame);
      }
      return _result;
    }

    /// simple_tree_sum t sums all leaf values.
    __attribute__((pure)) unsigned int simple_tree_sum() const {
      const simple_tree *_self = this;

      struct _Enter {
        const simple_tree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename simple_tree::SNode &>()
                     .d_a0.get()) _s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const simple_tree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename simple_tree::SLeaf &_args)
                              -> void { _result = _args.d_a0; },
                          [&](const typename simple_tree::SNode &_args)
                              -> void {
                            _stack.emplace_back(_Call1{_args.d_a0.get()});
                            _stack.emplace_back(_Enter{_args.d_a1.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.emplace_back(_Call2{_result});
                  _stack.emplace_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) { _result = (_result + _f._s0); }},
            _frame);
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<simple_tree>, T1,
                     std::shared_ptr<simple_tree>, T1>
                  F1>
    T1 simple_tree_rec(F0 &&f, F1 &&f0) const {
      const simple_tree *_self = this;

      struct _Enter {
        const simple_tree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename simple_tree::SNode &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename simple_tree::SNode &>().d_a1) _s1;
        decltype(std::declval<const typename simple_tree::SNode &>().d_a0) _s2;
      };

      struct _Call2 {
        T1 _s0;
        decltype(std::declval<const typename simple_tree::SNode &>().d_a1) _s1;
        decltype(std::declval<const typename simple_tree::SNode &>().d_a0) _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const simple_tree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename simple_tree::SLeaf &_args)
                              -> void { _result = f(_args.d_a0); },
                          [&](const typename simple_tree::SNode &_args)
                              -> void {
                            _stack.emplace_back(_Call1{_args.d_a0.get(),
                                                       _args.d_a1, _args.d_a0});
                            _stack.emplace_back(_Enter{_args.d_a1.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.emplace_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = f0(_f._s2, _result, _f._s1, _f._s0);
                }},
            _frame);
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<simple_tree>, T1,
                     std::shared_ptr<simple_tree>, T1>
                  F1>
    T1 simple_tree_rect(F0 &&f, F1 &&f0) const {
      const simple_tree *_self = this;

      struct _Enter {
        const simple_tree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename simple_tree::SNode &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename simple_tree::SNode &>().d_a1) _s1;
        decltype(std::declval<const typename simple_tree::SNode &>().d_a0) _s2;
      };

      struct _Call2 {
        T1 _s0;
        decltype(std::declval<const typename simple_tree::SNode &>().d_a1) _s1;
        decltype(std::declval<const typename simple_tree::SNode &>().d_a0) _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const simple_tree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename simple_tree::SLeaf &_args)
                              -> void { _result = f(_args.d_a0); },
                          [&](const typename simple_tree::SNode &_args)
                              -> void {
                            _stack.emplace_back(_Call1{_args.d_a0.get(),
                                                       _args.d_a1, _args.d_a0});
                            _stack.emplace_back(_Enter{_args.d_a1.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.emplace_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = f0(_f._s2, _result, _f._s1, _f._s0);
                }},
            _frame);
      }
      return _result;
    }
  };

  /// Helper: compute minimum of three values.
  __attribute__((pure)) static unsigned int
  min3(const unsigned int a, const unsigned int b, const unsigned int c);
  /// Helper: compute maximum of three values.
  __attribute__((pure)) static unsigned int
  max3(const unsigned int a, const unsigned int b, const unsigned int c);
  /// tree_min_max t finds minimum and maximum values in tree.
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  tree_min_max(const std::shared_ptr<tree<unsigned int>> &t);
  /// all_paths_sum t sums all root-to-leaf path sums.
  __attribute__((pure)) static unsigned int
  all_paths_sum(const std::shared_ptr<tree<unsigned int>> &t);
  /// tree_contains x t checks if value exists in tree.
  __attribute__((pure)) static bool
  tree_contains(const unsigned int x,
                const std::shared_ptr<tree<unsigned int>> &t);
};

#endif // INCLUDED_LOOPIFY_TREES
