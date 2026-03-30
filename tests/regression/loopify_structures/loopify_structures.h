#ifndef INCLUDED_LOOPIFY_STRUCTURES
#define INCLUDED_LOOPIFY_STRUCTURES

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

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
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

/// Nested and complex data structures.
struct LoopifyStructures {
  /// Nested list: elements or nested lists.
  struct nested {
    // TYPES
    struct Elem {
      unsigned int d_a0;
    };

    struct NList {
      std::shared_ptr<List<std::shared_ptr<nested>>> d_a0;
    };

    using variant_t = std::variant<Elem, NList>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit nested(Elem _v) : d_v_(std::move(_v)) {}

    explicit nested(NList _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<nested> elem(unsigned int a0) {
      return std::make_shared<nested>(Elem{std::move(a0)});
    }

    static std::shared_ptr<nested>
    nlist(const std::shared_ptr<List<std::shared_ptr<nested>>> &a0) {
      return std::make_shared<nested>(NList{a0});
    }

    static std::shared_ptr<nested>
    nlist(std::shared_ptr<List<std::shared_ptr<nested>>> &&a0) {
      return std::make_shared<nested>(NList{std::move(a0)});
    }

    static std::unique_ptr<nested> elem_uptr(unsigned int a0) {
      return std::make_unique<nested>(Elem{std::move(a0)});
    }

    static std::unique_ptr<nested>
    nlist_uptr(const std::shared_ptr<List<std::shared_ptr<nested>>> &a0) {
      return std::make_unique<nested>(NList{a0});
    }

    static std::unique_ptr<nested>
    nlist_uptr(std::shared_ptr<List<std::shared_ptr<nested>>> &&a0) {
      return std::make_unique<nested>(NList{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// nested_flatten n flattens to a regular list.
    std::shared_ptr<List<unsigned int>> nested_flatten() const {
      return std::visit(Overloaded{[](const typename nested::Elem _args)
                                       -> std::shared_ptr<List<unsigned int>> {
                                     return List<unsigned int>::cons(
                                         _args.d_a0, List<unsigned int>::nil());
                                   },
                                   [](const typename nested::NList _args)
                                       -> std::shared_ptr<List<unsigned int>> {
                                     return flatten_nested_list_fuel(
                                         1000u, _args.d_a0);
                                   }},
                        this->v());
    }

    /// nested_depth n computes maximum nesting depth.
    __attribute__((pure)) unsigned int nested_depth() const {
      return std::visit(
          Overloaded{[](const typename nested::Elem _args) -> unsigned int {
                       return 0u;
                     },
                     [](const typename nested::NList _args) -> unsigned int {
                       return (depth_nested_list_fuel(1000u, _args.d_a0) + 1);
                     }},
          this->v());
    }

    /// nested_sum n sums all elements in a nested structure.
    __attribute__((pure)) unsigned int nested_sum() const {
      return std::visit(
          Overloaded{[](const typename nested::Elem _args) -> unsigned int {
                       return _args.d_a0;
                     },
                     [](const typename nested::NList _args) -> unsigned int {
                       return sum_nested_list_fuel(1000u, _args.d_a0);
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<List<std::shared_ptr<nested>>>> F1>
    T1 nested_rec(F0 &&f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename nested::Elem _args) -> T1 {
                       return f(_args.d_a0);
                     },
                     [&](const typename nested::NList _args) -> T1 {
                       return f0(_args.d_a0);
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<List<std::shared_ptr<nested>>>> F1>
    T1 nested_rect(F0 &&f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename nested::Elem _args) -> T1 {
                       return f(_args.d_a0);
                     },
                     [&](const typename nested::NList _args) -> T1 {
                       return f0(_args.d_a0);
                     }},
          this->v());
    }
  };

  /// Helper: sum all elements in a list of nested structures.
  /// Handles both tree and list levels in one function for full loopification.
  __attribute__((pure)) static unsigned int
  sum_nested_list_fuel(const unsigned int fuel,
                       const std::shared_ptr<List<std::shared_ptr<nested>>> &l);
  /// Helper: compute max depth among a list of nested structures.
  __attribute__((pure)) static unsigned int depth_nested_list_fuel(
      const unsigned int fuel,
      const std::shared_ptr<List<std::shared_ptr<nested>>> &l);
  /// Helper: flatten a list of nested structures to a flat list of nats.
  static std::shared_ptr<List<unsigned int>> flatten_nested_list_fuel(
      const unsigned int fuel,
      const std::shared_ptr<List<std::shared_ptr<nested>>> &l);

  /// Quadtree: leaf or 4-way branch.
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

    static std::unique_ptr<quadtree> qleaf_uptr(unsigned int a0) {
      return std::make_unique<quadtree>(QLeaf{std::move(a0)});
    }

    static std::unique_ptr<quadtree>
    quad_uptr(const std::shared_ptr<quadtree> &a0,
              const std::shared_ptr<quadtree> &a1,
              const std::shared_ptr<quadtree> &a2,
              const std::shared_ptr<quadtree> &a3) {
      return std::make_unique<quadtree>(Quad{a0, a1, a2, a3});
    }

    static std::unique_ptr<quadtree> quad_uptr(std::shared_ptr<quadtree> &&a0,
                                               std::shared_ptr<quadtree> &&a1,
                                               std::shared_ptr<quadtree> &&a2,
                                               std::shared_ptr<quadtree> &&a3) {
      return std::make_unique<quadtree>(
          Quad{std::move(a0), std::move(a1), std::move(a2), std::move(a3)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// quad_map f t applies function to all leaves.
    template <MapsTo<unsigned int, unsigned int> F0>
    std::shared_ptr<quadtree> quad_map(F0 &&f) const {
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
        std::shared_ptr<quadtree> _s0;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      struct _Call3 {
        std::shared_ptr<quadtree> _s0;
        std::shared_ptr<quadtree> _s1;
        const quadtree *_s2;
      };

      struct _Call4 {
        std::shared_ptr<quadtree> _s0;
        std::shared_ptr<quadtree> _s1;
        std::shared_ptr<quadtree> _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
      std::shared_ptr<quadtree> _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const quadtree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename quadtree::QLeaf _args) -> void {
                            _result = quadtree::qleaf(f(_args.d_a0));
                          },
                          [&](const typename quadtree::Quad _args) -> void {
                            _stack.push_back(_Call1{_args.d_a2.get(),
                                                    _args.d_a1.get(),
                                                    _args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a3.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _stack.push_back(_Call3{_f._s0, _result, _f._s2});
                  _stack.push_back(_Enter{_f._s1});
                },
                [&](_Call3 _f) {
                  _stack.push_back(_Call4{_f._s0, _f._s1, _result});
                  _stack.push_back(_Enter{_f._s2});
                },
                [&](_Call4 _f) {
                  _result = quadtree::quad(_result, _f._s2, _f._s1, _f._s0);
                }},
            _frame);
      }
      return _result;
    }

    /// quad_depth t computes quadtree depth.
    __attribute__((pure)) unsigned int quad_depth() const {
      const quadtree *_self = this;

      struct _Enter {
        const quadtree *_self;
      };

      struct _Call1 {
        const typename quadtree::Quad _s0;
      };

      struct _Call2 {
        const typename quadtree::Quad _s0;
        unsigned int _s1;
      };

      struct _Call3 {
        const typename quadtree::Quad _s0;
        unsigned int _s1;
        unsigned int _s2;
      };

      struct _Call4 {
        unsigned int _s0;
        unsigned int _s1;
        unsigned int _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const quadtree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename quadtree::QLeaf _args) -> void {
                            _result = 0u;
                          },
                          [&](const typename quadtree::Quad _args) -> void {
                            _stack.push_back(_Call1{_args});
                            _stack.push_back(_Enter{_args.d_a0.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  const typename quadtree::Quad _args = _f._s0;
                  unsigned int d1 = _result;
                  _stack.push_back(_Call2{_args, d1});
                  _stack.push_back(_Enter{_args.d_a1.get()});
                },
                [&](_Call2 _f) {
                  const typename quadtree::Quad _args = _f._s0;
                  unsigned int d1 = _f._s1;
                  unsigned int d2 = _result;
                  _stack.push_back(_Call3{_args, d1, d2});
                  _stack.push_back(_Enter{_args.d_a2.get()});
                },
                [&](_Call3 _f) {
                  const typename quadtree::Quad _args = _f._s0;
                  unsigned int d1 = _f._s1;
                  unsigned int d2 = _f._s2;
                  unsigned int d3 = _result;
                  _stack.push_back(_Call4{d1, d2, d3});
                  _stack.push_back(_Enter{_args.d_a3.get()});
                },
                [&](_Call4 _f) {
                  unsigned int d1 = _f._s0;
                  unsigned int d2 = _f._s1;
                  unsigned int d3 = _f._s2;
                  unsigned int d4 = _result;
                  _result = ([&]() {
                    if ([&]() {
                          if (d1 <= d2) {
                            return std::move(d2);
                          } else {
                            return std::move(d1);
                          }
                        }() <=
                        [&]() {
                          if (d3 <= d4) {
                            return std::move(d4);
                          } else {
                            return std::move(d3);
                          }
                        }()) {
                      if (d3 <= d4) {
                        return std::move(d4);
                      } else {
                        return std::move(d3);
                      }
                    } else {
                      if (d1 <= d2) {
                        return std::move(d2);
                      } else {
                        return std::move(d1);
                      }
                    }
                  }() + 1);
                }},
            _frame);
      }
      return _result;
    }

    /// quad_sum t sums all values in quadtree.
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
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const quadtree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename quadtree::QLeaf _args) -> void {
                            _result = _args.d_a0;
                          },
                          [&](const typename quadtree::Quad _args) -> void {
                            _stack.push_back(_Call1{_args.d_a2.get(),
                                                    _args.d_a1.get(),
                                                    _args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a3.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _stack.push_back(_Call3{_f._s0, _result, _f._s2});
                  _stack.push_back(_Enter{_f._s1});
                },
                [&](_Call3 _f) {
                  _stack.push_back(_Call4{_f._s0, _f._s1, _result});
                  _stack.push_back(_Enter{_f._s2});
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
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const quadtree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename quadtree::QLeaf _args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename quadtree::Quad _args) -> void {
                            _stack.push_back(
                                _Call1{_args.d_a2.get(), _args.d_a1.get(),
                                       _args.d_a0.get(), _args.d_a3, _args.d_a2,
                                       _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a3.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3,
                                          _f._s4, _f._s5, _f._s6});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _stack.push_back(_Call3{_f._s0, _result, _f._s2, _f._s3,
                                          _f._s4, _f._s5, _f._s6});
                  _stack.push_back(_Enter{_f._s1});
                },
                [&](_Call3 _f) {
                  _stack.push_back(_Call4{_f._s0, _f._s1, _result, _f._s3,
                                          _f._s4, _f._s5, _f._s6});
                  _stack.push_back(_Enter{_f._s2});
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
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const quadtree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename quadtree::QLeaf _args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename quadtree::Quad _args) -> void {
                            _stack.push_back(
                                _Call1{_args.d_a2.get(), _args.d_a1.get(),
                                       _args.d_a0.get(), _args.d_a3, _args.d_a2,
                                       _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a3.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3,
                                          _f._s4, _f._s5, _f._s6});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _stack.push_back(_Call3{_f._s0, _result, _f._s2, _f._s3,
                                          _f._s4, _f._s5, _f._s6});
                  _stack.push_back(_Enter{_f._s1});
                },
                [&](_Call3 _f) {
                  _stack.push_back(_Call4{_f._s0, _f._s1, _result, _f._s3,
                                          _f._s4, _f._s5, _f._s6});
                  _stack.push_back(_Enter{_f._s2});
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

  /// find_opt p l finds first element satisfying predicate, returns option.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::optional<unsigned int>
  find_opt(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    std::optional<unsigned int> _result;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                              _result = std::optional<unsigned int>();
                              _continue = false;
                            },
                            [&](const typename List<unsigned int>::Cons _args) {
                              if (p(_args.d_a0)) {
                                _result = std::make_optional<unsigned int>(
                                    _args.d_a0);
                                _continue = false;
                              } else {
                                _loop_l = _args.d_a1;
                              }
                            }},
                 _loop_l->v());
    }
    return _result;
  }

  /// map_opt f l maps option-returning function and filters out Nones.
  template <MapsTo<std::optional<unsigned int>, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  map_opt(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil _args) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::nil();
                } else {
                  _head = List<unsigned int>::nil();
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons _args) {
                if (f(_args.d_a0).has_value()) {
                  unsigned int y = *f(_args.d_a0);
                  auto _cell = List<unsigned int>::cons(y, nullptr);
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  _loop_l = _args.d_a1;
                } else {
                  _loop_l = _args.d_a1;
                }
              }},
          _loop_l->v());
    }
    return _head;
  }

  /// filter_map p f l filters and maps in one pass.
  template <MapsTo<bool, unsigned int> F0,
            MapsTo<unsigned int, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>>
  filter_map(F0 &&p, F1 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil _args) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::nil();
                } else {
                  _head = List<unsigned int>::nil();
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons _args) {
                if (p(_args.d_a0)) {
                  auto _cell = List<unsigned int>::cons(f(_args.d_a0), nullptr);
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  _loop_l = _args.d_a1;
                } else {
                  _loop_l = _args.d_a1;
                }
              }},
          _loop_l->v());
    }
    return _head;
  }

  /// find_first_some l finds first Some value in list of options.
  __attribute__((pure)) static std::optional<unsigned int>
  find_first_some(const std::shared_ptr<List<std::optional<unsigned int>>> &l);

  /// Tree type with values in leaves.
  struct ltree {
    // TYPES
    struct LLeaf {
      unsigned int d_a0;
    };

    struct LNode {
      unsigned int d_a0;
      std::shared_ptr<ltree> d_a1;
      std::shared_ptr<ltree> d_a2;
    };

    using variant_t = std::variant<LLeaf, LNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit ltree(LLeaf _v) : d_v_(std::move(_v)) {}

    explicit ltree(LNode _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<ltree> lleaf(unsigned int a0) {
      return std::make_shared<ltree>(LLeaf{std::move(a0)});
    }

    static std::shared_ptr<ltree> lnode(unsigned int a0,
                                        const std::shared_ptr<ltree> &a1,
                                        const std::shared_ptr<ltree> &a2) {
      return std::make_shared<ltree>(LNode{std::move(a0), a1, a2});
    }

    static std::shared_ptr<ltree> lnode(unsigned int a0,
                                        std::shared_ptr<ltree> &&a1,
                                        std::shared_ptr<ltree> &&a2) {
      return std::make_shared<ltree>(
          LNode{std::move(a0), std::move(a1), std::move(a2)});
    }

    static std::unique_ptr<ltree> lleaf_uptr(unsigned int a0) {
      return std::make_unique<ltree>(LLeaf{std::move(a0)});
    }

    static std::unique_ptr<ltree> lnode_uptr(unsigned int a0,
                                             const std::shared_ptr<ltree> &a1,
                                             const std::shared_ptr<ltree> &a2) {
      return std::make_unique<ltree>(LNode{std::move(a0), a1, a2});
    }

    static std::unique_ptr<ltree> lnode_uptr(unsigned int a0,
                                             std::shared_ptr<ltree> &&a1,
                                             std::shared_ptr<ltree> &&a2) {
      return std::make_unique<ltree>(
          LNode{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, std::shared_ptr<ltree>, T1,
                     std::shared_ptr<ltree>, T1>
                  F1>
    T1 ltree_rec(F0 &&f, F1 &&f0) const {
      const ltree *_self = this;

      struct _Enter {
        const ltree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename ltree::LNode &>().d_a1.get()) _s0;
        decltype(std::declval<const typename ltree::LNode &>().d_a2) _s1;
        decltype(std::declval<const typename ltree::LNode &>().d_a1) _s2;
        decltype(std::declval<const typename ltree::LNode &>().d_a0) _s3;
      };

      struct _Call2 {
        T1 _s0;
        decltype(std::declval<const typename ltree::LNode &>().d_a2) _s1;
        decltype(std::declval<const typename ltree::LNode &>().d_a1) _s2;
        decltype(std::declval<const typename ltree::LNode &>().d_a0) _s3;
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
                  const ltree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename ltree::LLeaf _args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename ltree::LNode _args) -> void {
                            _stack.push_back(_Call1{_args.d_a1.get(),
                                                    _args.d_a2, _args.d_a1,
                                                    _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = f0(_f._s3, _f._s2, _result, _f._s1, _f._s0);
                }},
            _frame);
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, std::shared_ptr<ltree>, T1,
                     std::shared_ptr<ltree>, T1>
                  F1>
    T1 ltree_rect(F0 &&f, F1 &&f0) const {
      const ltree *_self = this;

      struct _Enter {
        const ltree *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename ltree::LNode &>().d_a1.get()) _s0;
        decltype(std::declval<const typename ltree::LNode &>().d_a2) _s1;
        decltype(std::declval<const typename ltree::LNode &>().d_a1) _s2;
        decltype(std::declval<const typename ltree::LNode &>().d_a0) _s3;
      };

      struct _Call2 {
        T1 _s0;
        decltype(std::declval<const typename ltree::LNode &>().d_a2) _s1;
        decltype(std::declval<const typename ltree::LNode &>().d_a1) _s2;
        decltype(std::declval<const typename ltree::LNode &>().d_a0) _s3;
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
                  const ltree *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename ltree::LLeaf _args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename ltree::LNode _args) -> void {
                            _stack.push_back(_Call1{_args.d_a1.get(),
                                                    _args.d_a2, _args.d_a1,
                                                    _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = f0(_f._s3, _f._s2, _result, _f._s1, _f._s0);
                }},
            _frame);
      }
      return _result;
    }
  };

  /// ltree_max t1 t2 element-wise max of two leaf-trees.
  static std::shared_ptr<ltree> ltree_max(std::shared_ptr<ltree> t1,
                                          std::shared_ptr<ltree> t2);
};

#endif // INCLUDED_LOOPIFY_STRUCTURES
