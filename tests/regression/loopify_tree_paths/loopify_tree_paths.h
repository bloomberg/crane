#ifndef INCLUDED_LOOPIFY_TREE_PATHS
#define INCLUDED_LOOPIFY_TREE_PATHS

#include <algorithm>
#include <memory>
#include <optional>
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
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

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
              [&](const typename List<t_A>::Nil _args) {
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = m;
                } else {
                  _head = m;
                }
                _continue = false;
              },
              [&](const typename List<t_A>::Cons _args) {
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

struct LoopifyTreePaths {
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
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

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

    std::shared_ptr<List<unsigned int>> flatten_paths() const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename tree::Node &>().d_a0.get()) _s0;
        decltype(std::declval<const typename tree::Node &>().d_a1) _s1;
      };

      struct _Call2 {
        std::shared_ptr<List<unsigned int>> _s0;
        decltype(std::declval<const typename tree::Node &>().d_a1) _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      std::shared_ptr<List<unsigned int>> _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const tree *_self = _f._self;
                  std::visit(
                      Overloaded{[&](const typename tree::Leaf _args) -> void {
                                   _result = List<unsigned int>::nil();
                                 },
                                 [&](const typename tree::Node _args) -> void {
                                   _stack.push_back(
                                       _Call1{_args.d_a0.get(), _args.d_a1});
                                   _stack.push_back(_Enter{_args.d_a2.get()});
                                 }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result =
                      List<unsigned int>::cons(_f._s1, _result->app(_f._s0));
                }},
            _frame);
      }
      return _result;
    }

    __attribute__((pure)) unsigned int max_path_sum() const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename tree::Node &>().d_a0.get()) _s0;
        decltype(std::declval<const typename tree::Node &>().d_a1) _s1;
      };

      struct _Call2 {
        unsigned int _s0;
        decltype(std::declval<const typename tree::Node &>().d_a1) _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{[&](_Enter _f) {
                         const tree *_self = _f._self;
                         std::visit(
                             Overloaded{
                                 [&](const typename tree::Leaf _args) -> void {
                                   _result = 0u;
                                 },
                                 [&](const typename tree::Node _args) -> void {
                                   _stack.push_back(
                                       _Call1{_args.d_a0.get(), _args.d_a1});
                                   _stack.push_back(_Enter{_args.d_a2.get()});
                                 }},
                             _self->v());
                       },
                       [&](_Call1 _f) {
                         _stack.push_back(_Call2{_result, _f._s1});
                         _stack.push_back(_Enter{_f._s0});
                       },
                       [&](_Call2 _f) {
                         _result = (_f._s1 + std::max(_result, _f._s0));
                       }},
            _frame);
      }
      return _result;
    }

    __attribute__((pure)) std::optional<std::shared_ptr<List<unsigned int>>>
    find_path_sum(const unsigned int acc, const unsigned int target) const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
        const unsigned int acc;
      };

      struct _Call1 {
        const typename tree::Node _s0;
        const unsigned int _s1;
        unsigned int _s2;
      };

      struct _Call2 {
        const typename tree::Node _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      std::optional<std::shared_ptr<List<unsigned int>>> _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self, acc});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const tree *_self = _f._self;
                  const unsigned int acc = _f.acc;
                  std::visit(
                      Overloaded{
                          [&](const typename tree::Leaf _args) -> void {
                            if (acc == target) {
                              _result = std::make_optional<
                                  std::shared_ptr<List<unsigned int>>>(
                                  List<unsigned int>::nil());
                            } else {
                              _result = std::optional<
                                  std::shared_ptr<List<unsigned int>>>();
                            }
                          },
                          [&](const typename tree::Node _args) -> void {
                            unsigned int new_acc = (acc + _args.d_a1);
                            _stack.push_back(_Call1{_args, target, new_acc});
                            _stack.push_back(_Enter{_args.d_a0.get(), new_acc});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  const typename tree::Node _args = _f._s0;
                  const unsigned int target = _f._s1;
                  unsigned int new_acc = _f._s2;
                  if (_result.has_value()) {
                    std::shared_ptr<List<unsigned int>> path = *_result;
                    _result =
                        std::make_optional<std::shared_ptr<List<unsigned int>>>(
                            List<unsigned int>::cons(_args.d_a1, path));
                  } else {
                    _stack.push_back(_Call2{_args});
                    _stack.push_back(_Enter{_args.d_a2.get(), new_acc});
                  }
                },
                [&](_Call2 _f) {
                  const typename tree::Node _args = _f._s0;
                  if (_result.has_value()) {
                    std::shared_ptr<List<unsigned int>> path = *_result;
                    _result =
                        std::make_optional<std::shared_ptr<List<unsigned int>>>(
                            List<unsigned int>::cons(_args.d_a1, path));
                  } else {
                    _result =
                        std::optional<std::shared_ptr<List<unsigned int>>>();
                  }
                }},
            _frame);
      }
      return _result;
    }

    __attribute__((pure)) unsigned int
    count_paths_sum(const unsigned int target) const {
      return this->count_paths_sum_aux(0u, target);
    }

    __attribute__((pure)) unsigned int
    count_paths_sum_aux(const unsigned int acc,
                        const unsigned int target) const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
        const unsigned int acc;
      };

      struct _Call1 {
        decltype(std::declval<const typename tree::Node &>().d_a0.get()) _s0;
        unsigned int _s1;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self, acc});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const tree *_self = _f._self;
                  const unsigned int acc = _f.acc;
                  std::visit(
                      Overloaded{
                          [&](const typename tree::Leaf _args) -> void {
                            if (acc == target) {
                              _result = 1u;
                            } else {
                              _result = 0u;
                            }
                          },
                          [&](const typename tree::Node _args) -> void {
                            unsigned int new_acc = (acc + _args.d_a1);
                            _stack.push_back(_Call1{_args.d_a0.get(), new_acc});
                            _stack.push_back(_Enter{_args.d_a2.get(), new_acc});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result});
                  _stack.push_back(_Enter{_f._s0, _f._s1});
                },
                [&](_Call2 _f) { _result = (_result + _f._s0); }},
            _frame);
      }
      return _result;
    }

    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> paths() const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename tree::Node &>().d_a0.get()) _s0;
        decltype(std::declval<const typename tree::Node &>().d_a1) _s1;
        decltype(std::declval<const typename tree::Node &>().d_a1) _s2;
      };

      struct _Call2 {
        std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _s0;
        decltype(std::declval<const typename tree::Node &>().d_a1) _s1;
        decltype(std::declval<const typename tree::Node &>().d_a1) _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const tree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename tree::Leaf _args) -> void {
                            _result =
                                List<std::shared_ptr<List<unsigned int>>>::cons(
                                    List<unsigned int>::nil(),
                                    List<std::shared_ptr<List<unsigned int>>>::
                                        nil());
                          },
                          [&](const typename tree::Node _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a1});
                            _stack.push_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result =
                      map_cons(_f._s2, _result)->app(map_cons(_f._s1, _f._s0));
                }},
            _frame);
      }
      return _result;
    }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    struct _Enter {
      const std::shared_ptr<tree> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename tree::Node &>().d_a0) _s0;
      decltype(std::declval<const typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree::Node &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<tree> t = _f.t;
                std::visit(
                    Overloaded{[&](const typename tree::Leaf _args) -> void {
                                 _result = f;
                               },
                               [&](const typename tree::Node _args) -> void {
                                 _stack.push_back(_Call1{_args.d_a0, _args.d_a2,
                                                         _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a2});
                               }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
              }},
          _frame);
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
      decltype(std::declval<const typename tree::Node &>().d_a0) _s0;
      decltype(std::declval<const typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree::Node &>().d_a0) _s3;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename tree::Node &>().d_a2) _s1;
      decltype(std::declval<const typename tree::Node &>().d_a1) _s2;
      decltype(std::declval<const typename tree::Node &>().d_a0) _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<tree> t = _f.t;
                std::visit(
                    Overloaded{[&](const typename tree::Leaf _args) -> void {
                                 _result = f;
                               },
                               [&](const typename tree::Node _args) -> void {
                                 _stack.push_back(_Call1{_args.d_a0, _args.d_a2,
                                                         _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a2});
                               }},
                    t->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) {
                _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> map_cons(
      const unsigned int x,
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);

  struct bool_tree {
    // TYPES
    struct BLeaf {
      unsigned int d_a0;
    };

    struct BNode {
      std::shared_ptr<bool_tree> d_a0;
      std::shared_ptr<bool_tree> d_a1;
    };

    using variant_t = std::variant<BLeaf, BNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit bool_tree(BLeaf _v) : d_v_(std::move(_v)) {}

    explicit bool_tree(BNode _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<bool_tree> bleaf(unsigned int a0) {
      return std::make_shared<bool_tree>(BLeaf{std::move(a0)});
    }

    static std::shared_ptr<bool_tree>
    bnode(const std::shared_ptr<bool_tree> &a0,
          const std::shared_ptr<bool_tree> &a1) {
      return std::make_shared<bool_tree>(BNode{a0, a1});
    }

    static std::shared_ptr<bool_tree> bnode(std::shared_ptr<bool_tree> &&a0,
                                            std::shared_ptr<bool_tree> &&a1) {
      return std::make_shared<bool_tree>(BNode{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <MapsTo<bool, unsigned int> F0>
    __attribute__((pure)) bool and_search(F0 &&p) const {
      const bool_tree *_self = this;

      struct _Enter {
        const bool_tree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename bool_tree::BNode &>()
                     .d_a0.get()) _s0;
      };

      struct _Call2 {
        bool _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      bool _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const bool_tree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename bool_tree::BLeaf _args) -> void {
                            _result = p(_args.d_a0);
                          },
                          [&](const typename bool_tree::BNode _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) { _result = (_result && _f._s0); }},
            _frame);
      }
      return _result;
    }

    template <MapsTo<bool, unsigned int> F0>
    __attribute__((pure)) bool or_search(F0 &&p) const {
      const bool_tree *_self = this;

      struct _Enter {
        const bool_tree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename bool_tree::BNode &>()
                     .d_a0.get()) _s0;
      };

      struct _Call2 {
        bool _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      bool _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const bool_tree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename bool_tree::BLeaf _args) -> void {
                            _result = p(_args.d_a0);
                          },
                          [&](const typename bool_tree::BNode _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) { _result = (_result || _f._s0); }},
            _frame);
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<bool_tree>, T1,
                     std::shared_ptr<bool_tree>, T1>
                  F1>
    T1 bool_tree_rec(F0 &&f, F1 &&f0) const {
      const bool_tree *_self = this;

      struct _Enter {
        const bool_tree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename bool_tree::BNode &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename bool_tree::BNode &>().d_a1) _s1;
        decltype(std::declval<const typename bool_tree::BNode &>().d_a0) _s2;
      };

      struct _Call2 {
        T1 _s0;
        decltype(std::declval<const typename bool_tree::BNode &>().d_a1) _s1;
        decltype(std::declval<const typename bool_tree::BNode &>().d_a0) _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const bool_tree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename bool_tree::BLeaf _args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename bool_tree::BNode _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = f0(_f._s2, _result, _f._s1, _f._s0);
                }},
            _frame);
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<bool_tree>, T1,
                     std::shared_ptr<bool_tree>, T1>
                  F1>
    T1 bool_tree_rect(F0 &&f, F1 &&f0) const {
      const bool_tree *_self = this;

      struct _Enter {
        const bool_tree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename bool_tree::BNode &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename bool_tree::BNode &>().d_a1) _s1;
        decltype(std::declval<const typename bool_tree::BNode &>().d_a0) _s2;
      };

      struct _Call2 {
        T1 _s0;
        decltype(std::declval<const typename bool_tree::BNode &>().d_a1) _s1;
        decltype(std::declval<const typename bool_tree::BNode &>().d_a0) _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const bool_tree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename bool_tree::BLeaf _args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename bool_tree::BNode _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = f0(_f._s2, _result, _f._s1, _f._s0);
                }},
            _frame);
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_TREE_PATHS
