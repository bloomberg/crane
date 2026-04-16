#ifndef INCLUDED_LOOPIFY_STRUCTURES
#define INCLUDED_LOOPIFY_STRUCTURES

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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
    std::shared_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    while (true) {
      if (std::holds_alternative<typename List<t_A>::Nil>(_loop_self->v())) {
        *_write = m;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<t_A>::Cons>(_loop_self->v());
        auto _cell = List<t_A>::cons(d_a0, nullptr);
        *_write = _cell;
        _write = &std::get<typename List<t_A>::Cons>(_cell->v_mut()).d_a1;
        _loop_self = d_a1.get();
        continue;
      }
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

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// nested_flatten n flattens to a regular list.
    std::shared_ptr<List<unsigned int>> nested_flatten() const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        const auto &[d_a0] = std::get<typename nested::Elem>(this->v());
        return List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
      } else {
        const auto &[d_a0] = std::get<typename nested::NList>(this->v());
        return flatten_nested_list_fuel(1000u, d_a0);
      }
    }

    /// nested_depth n computes maximum nesting depth.
    __attribute__((pure)) unsigned int nested_depth() const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        return 0u;
      } else {
        const auto &[d_a0] = std::get<typename nested::NList>(this->v());
        return (depth_nested_list_fuel(1000u, d_a0) + 1);
      }
    }

    /// nested_sum n sums all elements in a nested structure.
    __attribute__((pure)) unsigned int nested_sum() const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        const auto &[d_a0] = std::get<typename nested::Elem>(this->v());
        return d_a0;
      } else {
        const auto &[d_a0] = std::get<typename nested::NList>(this->v());
        return sum_nested_list_fuel(1000u, d_a0);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<List<std::shared_ptr<nested>>>> F1>
    T1 nested_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        const auto &[d_a0] = std::get<typename nested::Elem>(this->v());
        return f(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename nested::NList>(this->v());
        return f0(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<List<std::shared_ptr<nested>>>> F1>
    T1 nested_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        const auto &[d_a0] = std::get<typename nested::Elem>(this->v());
        return f(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename nested::NList>(this->v());
        return f0(d_a0);
      }
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
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const quadtree *_self = _f._self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_self->v())) {
            const auto &[d_a0] = std::get<typename quadtree::QLeaf>(_self->v());
            _result = quadtree::qleaf(f(d_a0));
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename quadtree::Quad>(_self->v());
            _stack.emplace_back(_Call1{d_a2.get(), d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _stack.emplace_back(_Call3{_f._s0, _result, _f._s2});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          const auto &_f = std::get<_Call3>(_frame);
          _stack.emplace_back(_Call4{_f._s0, _f._s1, _result});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          const auto &_f = std::get<_Call4>(_frame);
          _result = quadtree::quad(_result, _f._s2, _f._s1, _f._s0);
        }
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
        std::shared_ptr<quadtree> _s0;
        std::shared_ptr<quadtree> _s1;
        std::shared_ptr<quadtree> _s2;
      };

      struct _Call2 {
        unsigned int _s0;
        std::shared_ptr<quadtree> _s1;
        std::shared_ptr<quadtree> _s2;
      };

      struct _Call3 {
        unsigned int _s0;
        unsigned int _s1;
        std::shared_ptr<quadtree> _s2;
      };

      struct _Call4 {
        unsigned int _s0;
        unsigned int _s1;
        unsigned int _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const quadtree *_self = _f._self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_self->v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename quadtree::Quad>(_self->v());
            _stack.emplace_back(_Call1{d_a1, d_a2, d_a3});
            _stack.emplace_back(_Enter{d_a0.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          std::shared_ptr<quadtree> d_a1 = _f._s0;
          std::shared_ptr<quadtree> d_a2 = _f._s1;
          std::shared_ptr<quadtree> d_a3 = _f._s2;
          unsigned int d1 = _result;
          _stack.emplace_back(_Call2{d1, d_a2, d_a3});
          _stack.emplace_back(_Enter{d_a1.get()});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          unsigned int d1 = _f._s0;
          std::shared_ptr<quadtree> d_a2 = _f._s1;
          std::shared_ptr<quadtree> d_a3 = _f._s2;
          unsigned int d2 = _result;
          _stack.emplace_back(_Call3{d1, d2, d_a3});
          _stack.emplace_back(_Enter{d_a2.get()});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          const auto &_f = std::get<_Call3>(_frame);
          unsigned int d1 = _f._s0;
          unsigned int d2 = _f._s1;
          std::shared_ptr<quadtree> d_a3 = _f._s2;
          unsigned int d3 = _result;
          _stack.emplace_back(_Call4{d1, d2, d3});
          _stack.emplace_back(_Enter{d_a3.get()});
        } else {
          const auto &_f = std::get<_Call4>(_frame);
          unsigned int d1 = _f._s0;
          unsigned int d2 = _f._s1;
          unsigned int d3 = _f._s2;
          unsigned int d4 = _result;
          _result = ([&]() -> unsigned int {
            if ([&]() -> unsigned int {
                  if (d1 <= d2) {
                    return d2;
                  } else {
                    return d1;
                  }
                }() <= [&]() -> unsigned int {
                  if (d3 <= d4) {
                    return d4;
                  } else {
                    return d3;
                  }
                }()) {
              if (d3 <= d4) {
                return d4;
              } else {
                return d3;
              }
            } else {
              if (d1 <= d2) {
                return d2;
              } else {
                return d1;
              }
            }
          }() + 1);
        }
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
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const quadtree *_self = _f._self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_self->v())) {
            const auto &[d_a0] = std::get<typename quadtree::QLeaf>(_self->v());
            _result = d_a0;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename quadtree::Quad>(_self->v());
            _stack.emplace_back(_Call1{d_a2.get(), d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _stack.emplace_back(_Call3{_f._s0, _result, _f._s2});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          const auto &_f = std::get<_Call3>(_frame);
          _stack.emplace_back(_Call4{_f._s0, _f._s1, _result});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          const auto &_f = std::get<_Call4>(_frame);
          _result = (_result + (_f._s2 + (_f._s1 + _f._s0)));
        }
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
        std::shared_ptr<quadtree> _s3;
        std::shared_ptr<quadtree> _s4;
        std::shared_ptr<quadtree> _s5;
        std::shared_ptr<quadtree> _s6;
      };

      struct _Call2 {
        T1 _s0;
        const quadtree *_s1;
        const quadtree *_s2;
        std::shared_ptr<quadtree> _s3;
        std::shared_ptr<quadtree> _s4;
        std::shared_ptr<quadtree> _s5;
        std::shared_ptr<quadtree> _s6;
      };

      struct _Call3 {
        T1 _s0;
        T1 _s1;
        const quadtree *_s2;
        std::shared_ptr<quadtree> _s3;
        std::shared_ptr<quadtree> _s4;
        std::shared_ptr<quadtree> _s5;
        std::shared_ptr<quadtree> _s6;
      };

      struct _Call4 {
        T1 _s0;
        T1 _s1;
        T1 _s2;
        std::shared_ptr<quadtree> _s3;
        std::shared_ptr<quadtree> _s4;
        std::shared_ptr<quadtree> _s5;
        std::shared_ptr<quadtree> _s6;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const quadtree *_self = _f._self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_self->v())) {
            const auto &[d_a0] = std::get<typename quadtree::QLeaf>(_self->v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename quadtree::Quad>(_self->v());
            _stack.emplace_back(_Call1{d_a2.get(), d_a1.get(), d_a0.get(), d_a3,
                                       d_a2, d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(
              _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _stack.emplace_back(
              _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          const auto &_f = std::get<_Call3>(_frame);
          _stack.emplace_back(
              _Call4{_f._s0, _f._s1, _result, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          const auto &_f = std::get<_Call4>(_frame);
          _result = f0(_f._s6, _result, _f._s5, _f._s2, _f._s4, _f._s1, _f._s3,
                       _f._s0);
        }
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
        std::shared_ptr<quadtree> _s3;
        std::shared_ptr<quadtree> _s4;
        std::shared_ptr<quadtree> _s5;
        std::shared_ptr<quadtree> _s6;
      };

      struct _Call2 {
        T1 _s0;
        const quadtree *_s1;
        const quadtree *_s2;
        std::shared_ptr<quadtree> _s3;
        std::shared_ptr<quadtree> _s4;
        std::shared_ptr<quadtree> _s5;
        std::shared_ptr<quadtree> _s6;
      };

      struct _Call3 {
        T1 _s0;
        T1 _s1;
        const quadtree *_s2;
        std::shared_ptr<quadtree> _s3;
        std::shared_ptr<quadtree> _s4;
        std::shared_ptr<quadtree> _s5;
        std::shared_ptr<quadtree> _s6;
      };

      struct _Call4 {
        T1 _s0;
        T1 _s1;
        T1 _s2;
        std::shared_ptr<quadtree> _s3;
        std::shared_ptr<quadtree> _s4;
        std::shared_ptr<quadtree> _s5;
        std::shared_ptr<quadtree> _s6;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const quadtree *_self = _f._self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_self->v())) {
            const auto &[d_a0] = std::get<typename quadtree::QLeaf>(_self->v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename quadtree::Quad>(_self->v());
            _stack.emplace_back(_Call1{d_a2.get(), d_a1.get(), d_a0.get(), d_a3,
                                       d_a2, d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(
              _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _stack.emplace_back(
              _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          const auto &_f = std::get<_Call3>(_frame);
          _stack.emplace_back(
              _Call4{_f._s0, _f._s1, _result, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          const auto &_f = std::get<_Call4>(_frame);
          _result = f0(_f._s6, _result, _f._s5, _f._s2, _f._s4, _f._s1, _f._s3,
                       _f._s0);
        }
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
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        _result = std::optional<unsigned int>();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(d_a0)) {
          _result = std::make_optional<unsigned int>(d_a0);
          break;
        } else {
          _loop_l = d_a1;
        }
      }
    }
    return _result;
  }

  /// map_opt f l maps option-returning function and filters out Nones.
  template <MapsTo<std::optional<unsigned int>, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  map_opt(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> *_write = &_head;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write = List<unsigned int>::nil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        auto _cs = f(d_a0);
        if (_cs.has_value()) {
          const unsigned int &y = *_cs;
          auto _cell = List<unsigned int>::cons(y, nullptr);
          *_write = _cell;
          _write =
              &std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1;
          _loop_l = d_a1;
          continue;
        } else {
          _loop_l = d_a1;
          continue;
        }
      }
    }
    return _head;
  }

  /// filter_map p f l filters and maps in one pass.
  template <MapsTo<bool, unsigned int> F0,
            MapsTo<unsigned int, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>>
  filter_map(F0 &&p, F1 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> *_write = &_head;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write = List<unsigned int>::nil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(d_a0)) {
          auto _cell = List<unsigned int>::cons(f(d_a0), nullptr);
          *_write = _cell;
          _write =
              &std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1;
          _loop_l = d_a1;
          continue;
        } else {
          _loop_l = d_a1;
          continue;
        }
      }
    }
    return _head;
  }

  /// find_first_some l finds first Some value in list of options.
  __attribute__((pure)) static std::optional<unsigned int>
  find_first_some(const std::shared_ptr<List<std::optional<unsigned int>>> &l);

  /// Tree type with values in leaves.
  struct ltree : public std::enable_shared_from_this<ltree> {
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

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// ltree_max t1 t2 element-wise max of two leaf-trees.
    std::shared_ptr<ltree> ltree_max(std::shared_ptr<ltree> t2) const {
      const ltree *_self = this;

      struct _Enter {
        const ltree *_self;
        std::shared_ptr<ltree> t2;
      };

      struct _Call1 {
        ltree *_s0;
        std::shared_ptr<ltree> _s1;
        unsigned int _s2;
      };

      struct _Call2 {
        std::shared_ptr<ltree> _s0;
        unsigned int _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      std::shared_ptr<ltree> _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self, t2});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const ltree *_self = _f._self;
          std::shared_ptr<ltree> t2 = _f.t2;
          if (std::holds_alternative<typename ltree::LLeaf>(_self->v())) {
            const auto &[d_a0] = std::get<typename ltree::LLeaf>(_self->v());
            if (std::holds_alternative<typename ltree::LLeaf>(t2->v())) {
              const auto &[d_a00] = std::get<typename ltree::LLeaf>(t2->v());
              _result = ltree::lleaf([&]() -> unsigned int {
                if (d_a0 <= d_a00) {
                  return d_a00;
                } else {
                  return d_a0;
                }
              }());
            } else {
              _result = t2;
            }
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename ltree::LNode>(_self->v());
            if (std::holds_alternative<typename ltree::LLeaf>(t2->v())) {
              _result =
                  std::const_pointer_cast<ltree>(this->shared_from_this());
            } else {
              const auto &[d_a00, d_a10, d_a20] =
                  std::get<typename ltree::LNode>(t2->v());
              unsigned int max_val;
              if (d_a0 <= d_a00) {
                max_val = d_a00;
              } else {
                max_val = d_a0;
              }
              _stack.emplace_back(_Call1{d_a1.get(), d_a10, max_val});
              _stack.emplace_back(_Enter{d_a2.get(), d_a20});
            }
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s2});
          _stack.emplace_back(_Enter{_f._s0, _f._s1});
        } else {
          const auto &_f = std::get<_Call2>(_frame);
          _result = ltree::lnode(_f._s1, _result, _f._s0);
        }
      }
      return _result;
    }

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
        ltree *_s0;
        std::shared_ptr<ltree> _s1;
        std::shared_ptr<ltree> _s2;
        unsigned int _s3;
      };

      struct _Call2 {
        T1 _s0;
        std::shared_ptr<ltree> _s1;
        std::shared_ptr<ltree> _s2;
        unsigned int _s3;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const ltree *_self = _f._self;
          if (std::holds_alternative<typename ltree::LLeaf>(_self->v())) {
            const auto &[d_a0] = std::get<typename ltree::LLeaf>(_self->v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename ltree::LNode>(_self->v());
            _stack.emplace_back(_Call1{d_a1.get(), d_a2, d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call2>(_frame);
          _result = f0(_f._s3, _f._s2, _result, _f._s1, _f._s0);
        }
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
        ltree *_s0;
        std::shared_ptr<ltree> _s1;
        std::shared_ptr<ltree> _s2;
        unsigned int _s3;
      };

      struct _Call2 {
        T1 _s0;
        std::shared_ptr<ltree> _s1;
        std::shared_ptr<ltree> _s2;
        unsigned int _s3;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          const auto &_f = std::get<_Enter>(_frame);
          const ltree *_self = _f._self;
          if (std::holds_alternative<typename ltree::LLeaf>(_self->v())) {
            const auto &[d_a0] = std::get<typename ltree::LLeaf>(_self->v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename ltree::LNode>(_self->v());
            _stack.emplace_back(_Call1{d_a1.get(), d_a2, d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call2>(_frame);
          _result = f0(_f._s3, _f._s2, _result, _f._s1, _f._s0);
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_STRUCTURES
