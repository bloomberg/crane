#ifndef INCLUDED_LOOPIFY_STRUCTURES
#define INCLUDED_LOOPIFY_STRUCTURES

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{clone_as_value<t_A>(d_a0),
                            clone_as_value<std::unique_ptr<List<t_A>>>(d_a1)});
    }
  }

  template <typename _CloneT0>
  __attribute__((pure)) List<_CloneT0> clone_as() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<_CloneT0>(typename List<_CloneT0>::Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<_CloneT0>(typename List<_CloneT0>::Cons{
          clone_as_value<_CloneT0>(d_a0),
          clone_as_value<std::unique_ptr<List<_CloneT0>>>(d_a1)});
    }
  }

  // CREATORS
  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1.clone())});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(m);
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        _loop_self = d_a1.get();
        continue;
      }
    }
    return std::move(*(_head));
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
      List<std::unique_ptr<nested>> d_a0;
    };

    using variant_t = std::variant<Elem, NList>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    nested() {}

    explicit nested(Elem _v) : d_v_(std::move(_v)) {}

    explicit nested(NList _v) : d_v_(std::move(_v)) {}

    nested(const nested &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    nested(nested &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) nested &operator=(const nested &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) nested &operator=(nested &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) nested clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Elem>(_sv.v())) {
        const auto &[d_a0] = std::get<Elem>(_sv.v());
        return nested(Elem{d_a0});
      } else {
        const auto &[d_a0] = std::get<NList>(_sv.v());
        return nested(NList{d_a0});
      }
    }

    // CREATORS
    __attribute__((pure)) static nested elem(unsigned int a0) {
      return nested(Elem{std::move(a0)});
    }

    __attribute__((pure)) static nested nlist(List<nested> a0) {
      return nested(NList{clone_as_value<List<std::unique_ptr<nested>>>(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) nested *operator->() { return this; }

    __attribute__((pure)) const nested *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = nested(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// nested_flatten n flattens to a regular list.
    __attribute__((pure)) List<unsigned int> nested_flatten() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename nested::Elem>(_sv.v())) {
        const auto &[d_a0] = std::get<typename nested::Elem>(_sv.v());
        return List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
      } else {
        const auto &[d_a0] = std::get<typename nested::NList>(_sv.v());
        return flatten_nested_list_fuel(
            1000u, clone_as_value<List<LoopifyStructures::nested>>(d_a0));
      }
    }

    /// nested_depth n computes maximum nesting depth.
    __attribute__((pure)) unsigned int nested_depth() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename nested::Elem>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0] = std::get<typename nested::NList>(_sv.v());
        return (
            depth_nested_list_fuel(
                1000u, clone_as_value<List<LoopifyStructures::nested>>(d_a0)) +
            1);
      }
    }

    /// nested_sum n sums all elements in a nested structure.
    __attribute__((pure)) unsigned int nested_sum() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename nested::Elem>(_sv.v())) {
        const auto &[d_a0] = std::get<typename nested::Elem>(_sv.v());
        return d_a0;
      } else {
        const auto &[d_a0] = std::get<typename nested::NList>(_sv.v());
        return sum_nested_list_fuel(
            1000u, clone_as_value<List<LoopifyStructures::nested>>(d_a0));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, List<std::unique_ptr<nested>>> F1>
    T1 nested_rec(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename nested::Elem>(_sv.v())) {
        const auto &[d_a0] = std::get<typename nested::Elem>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename nested::NList>(_sv.v());
        return f0(clone_as_value<List<LoopifyStructures::nested>>(d_a0));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, List<std::unique_ptr<nested>>> F1>
    T1 nested_rect(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename nested::Elem>(_sv.v())) {
        const auto &[d_a0] = std::get<typename nested::Elem>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename nested::NList>(_sv.v());
        return f0(clone_as_value<List<LoopifyStructures::nested>>(d_a0));
      }
    }
  };

  /// Helper: sum all elements in a list of nested structures.
  /// Handles both tree and list levels in one function for full loopification.
  __attribute__((pure)) static unsigned int
  sum_nested_list_fuel(const unsigned int &fuel, const List<nested> &l);
  /// Helper: compute max depth among a list of nested structures.
  __attribute__((pure)) static unsigned int
  depth_nested_list_fuel(const unsigned int &fuel, const List<nested> &l);
  /// Helper: flatten a list of nested structures to a flat list of nats.
  __attribute__((pure)) static List<unsigned int>
  flatten_nested_list_fuel(const unsigned int &fuel, const List<nested> &l);

  /// Quadtree: leaf or 4-way branch.
  struct quadtree {
    // TYPES
    struct QLeaf {
      unsigned int d_a0;
    };

    struct Quad {
      std::unique_ptr<quadtree> d_a0;
      std::unique_ptr<quadtree> d_a1;
      std::unique_ptr<quadtree> d_a2;
      std::unique_ptr<quadtree> d_a3;
    };

    using variant_t = std::variant<QLeaf, Quad>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    quadtree() {}

    explicit quadtree(QLeaf _v) : d_v_(std::move(_v)) {}

    explicit quadtree(Quad _v) : d_v_(std::move(_v)) {}

    quadtree(const quadtree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    quadtree(quadtree &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) quadtree &operator=(const quadtree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) quadtree &operator=(quadtree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) quadtree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<QLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<QLeaf>(_sv.v());
        return quadtree(QLeaf{d_a0});
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3] = std::get<Quad>(_sv.v());
        return quadtree(Quad{clone_as_value<std::unique_ptr<quadtree>>(d_a0),
                             clone_as_value<std::unique_ptr<quadtree>>(d_a1),
                             clone_as_value<std::unique_ptr<quadtree>>(d_a2),
                             clone_as_value<std::unique_ptr<quadtree>>(d_a3)});
      }
    }

    // CREATORS
    __attribute__((pure)) static quadtree qleaf(unsigned int a0) {
      return quadtree(QLeaf{std::move(a0)});
    }

    __attribute__((pure)) static quadtree quad(const quadtree &a0,
                                               const quadtree &a1,
                                               const quadtree &a2,
                                               const quadtree &a3) {
      return quadtree(Quad{std::make_unique<quadtree>(a0.clone()),
                           std::make_unique<quadtree>(a1.clone()),
                           std::make_unique<quadtree>(a2.clone()),
                           std::make_unique<quadtree>(a3.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) quadtree *operator->() { return this; }

    __attribute__((pure)) const quadtree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = quadtree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// quad_map f t applies function to all leaves.
    template <MapsTo<unsigned int, unsigned int> F0>
    __attribute__((pure)) quadtree quad_map(F0 &&f) const {
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
        quadtree _s0;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      struct _Call3 {
        quadtree _s0;
        quadtree _s1;
        const quadtree *_s2;
      };

      struct _Call4 {
        quadtree _s0;
        quadtree _s1;
        quadtree _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
      quadtree _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = quadtree::qleaf(f(d_a0));
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_Call1{d_a2.get(), d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(_Call3{_f._s0, _result, _f._s2});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_f._s0, _f._s1, _result});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Call4>(_frame));
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
        quadtree _s0;
        quadtree _s1;
        quadtree _s2;
      };

      struct _Call2 {
        unsigned int _s0;
        quadtree _s1;
        quadtree _s2;
      };

      struct _Call3 {
        unsigned int _s0;
        unsigned int _s1;
        quadtree _s2;
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
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            quadtree d_a0_value =
                clone_as_value<LoopifyStructures::quadtree>(d_a0);
            quadtree d_a1_value =
                clone_as_value<LoopifyStructures::quadtree>(d_a1);
            quadtree d_a2_value =
                clone_as_value<LoopifyStructures::quadtree>(d_a2);
            quadtree d_a3_value =
                clone_as_value<LoopifyStructures::quadtree>(d_a3);
            _stack.emplace_back(_Call1{d_a1_value, d_a2_value, d_a3_value});
            _stack.emplace_back(_Enter{d_a0_value.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          quadtree d_a1_value = _f._s0;
          quadtree d_a2_value = _f._s1;
          quadtree d_a3_value = _f._s2;
          unsigned int d1 = _result;
          _stack.emplace_back(_Call2{d1, d_a2_value, d_a3_value});
          _stack.emplace_back(_Enter{d_a1_value.get()});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          unsigned int d1 = _f._s0;
          quadtree d_a2_value = _f._s1;
          quadtree d_a3_value = _f._s2;
          unsigned int d2 = _result;
          _stack.emplace_back(_Call3{d1, d2, d_a3_value});
          _stack.emplace_back(_Enter{d_a2_value.get()});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          unsigned int d1 = _f._s0;
          unsigned int d2 = _f._s1;
          quadtree d_a3_value = _f._s2;
          unsigned int d3 = _result;
          _stack.emplace_back(_Call4{d1, d2, d3});
          _stack.emplace_back(_Enter{d_a3_value.get()});
        } else {
          auto _f = std::move(std::get<_Call4>(_frame));
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
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = d_a0;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_Call1{d_a2.get(), d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(_Call3{_f._s0, _result, _f._s2});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_f._s0, _f._s1, _result});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Call4>(_frame));
          _result = (_result + (_f._s2 + (_f._s1 + _f._s0)));
        }
      }
      return _result;
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, quadtree, T1, quadtree, T1, quadtree, T1, quadtree, T1> F1>
    T1 quadtree_rec(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      struct _Enter {
        const quadtree *_self;
      };

      struct _Call1 {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
      };

      struct _Call2 {
        T1 _s0;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
      };

      struct _Call3 {
        T1 _s0;
        T1 _s1;
        const quadtree *_s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
      };

      struct _Call4 {
        T1 _s0;
        T1 _s1;
        T1 _s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
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
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_Call1{d_a2.get(), d_a1.get(), d_a0.get(),
                                       *(d_a3), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(
              _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(
              _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(
              _Call4{_f._s0, _f._s1, _result, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Call4>(_frame));
          _result = f0(_f._s6, _result, _f._s5, _f._s2, _f._s4, _f._s1, _f._s3,
                       _f._s0);
        }
      }
      return _result;
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, quadtree, T1, quadtree, T1, quadtree, T1, quadtree, T1> F1>
    T1 quadtree_rect(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      struct _Enter {
        const quadtree *_self;
      };

      struct _Call1 {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
      };

      struct _Call2 {
        T1 _s0;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
      };

      struct _Call3 {
        T1 _s0;
        T1 _s1;
        const quadtree *_s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
      };

      struct _Call4 {
        T1 _s0;
        T1 _s1;
        T1 _s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
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
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_Call1{d_a2.get(), d_a1.get(), d_a0.get(),
                                       *(d_a3), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(
              _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(
              _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(
              _Call4{_f._s0, _f._s1, _result, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Call4>(_frame));
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
  find_opt(F0 &&p, const List<unsigned int> &l) {
    std::optional<unsigned int> _result;
    List<unsigned int> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        _result = std::optional<unsigned int>();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        if (p(d_a0)) {
          _result = std::make_optional<unsigned int>(d_a0);
          break;
        } else {
          _loop_l = *(d_a1);
        }
      }
    }
    return _result;
  }

  /// map_opt f l maps option-returning function and filters out Nones.
  template <MapsTo<std::optional<unsigned int>, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  map_opt(F0 &&f, const List<unsigned int> &l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    List<unsigned int> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        auto _cs = f(d_a0);
        if (_cs.has_value()) {
          const unsigned int &y = *_cs;
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(y, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = *(d_a1);
          continue;
        } else {
          _loop_l = *(d_a1);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  /// filter_map p f l filters and maps in one pass.
  template <MapsTo<bool, unsigned int> F0,
            MapsTo<unsigned int, unsigned int> F1>
  __attribute__((pure)) static List<unsigned int>
  filter_map(F0 &&p, F1 &&f, const List<unsigned int> &l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    List<unsigned int> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        if (p(d_a0)) {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(f(d_a0), nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = *(d_a1);
          continue;
        } else {
          _loop_l = *(d_a1);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  /// find_first_some l finds first Some value in list of options.
  __attribute__((pure)) static std::optional<unsigned int>
  find_first_some(const List<std::optional<unsigned int>> &l);

  /// Tree type with values in leaves.
  struct ltree {
    // TYPES
    struct LLeaf {
      unsigned int d_a0;
    };

    struct LNode {
      unsigned int d_a0;
      std::unique_ptr<ltree> d_a1;
      std::unique_ptr<ltree> d_a2;
    };

    using variant_t = std::variant<LLeaf, LNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    ltree() {}

    explicit ltree(LLeaf _v) : d_v_(std::move(_v)) {}

    explicit ltree(LNode _v) : d_v_(std::move(_v)) {}

    ltree(const ltree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    ltree(ltree &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) ltree &operator=(const ltree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) ltree &operator=(ltree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) ltree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<LLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<LLeaf>(_sv.v());
        return ltree(LLeaf{d_a0});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<LNode>(_sv.v());
        return ltree(LNode{d_a0, clone_as_value<std::unique_ptr<ltree>>(d_a1),
                           clone_as_value<std::unique_ptr<ltree>>(d_a2)});
      }
    }

    // CREATORS
    __attribute__((pure)) static ltree lleaf(unsigned int a0) {
      return ltree(LLeaf{std::move(a0)});
    }

    __attribute__((pure)) static ltree lnode(unsigned int a0, const ltree &a1,
                                             const ltree &a2) {
      return ltree(LNode{std::move(a0), std::make_unique<ltree>(a1.clone()),
                         std::make_unique<ltree>(a2.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) ltree *operator->() { return this; }

    __attribute__((pure)) const ltree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = ltree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// ltree_max t1 t2 element-wise max of two leaf-trees.
    __attribute__((pure)) ltree ltree_max(ltree t2) const {
      const ltree *_self = this;

      struct _Enter {
        const ltree *_self;
        ltree t2;
      };

      struct _Call1 {
        ltree *_s0;
        ltree _s1;
        unsigned int _s2;
      };

      struct _Call2 {
        ltree _s0;
        unsigned int _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      ltree _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self, t2});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ltree *_self = _f._self;
          ltree t2 = _f.t2;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename ltree::LLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename ltree::LLeaf>(_sv.v());
            if (std::holds_alternative<typename ltree::LLeaf>(t2.v())) {
              const auto &[d_a00] = std::get<typename ltree::LLeaf>(t2.v());
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
                std::get<typename ltree::LNode>(_sv.v());
            if (std::holds_alternative<typename ltree::LLeaf>(t2.v())) {
              _result = *(_self);
            } else {
              const auto &[d_a00, d_a10, d_a20] =
                  std::get<typename ltree::LNode>(t2.v());
              unsigned int max_val;
              if (d_a0 <= d_a00) {
                max_val = d_a00;
              } else {
                max_val = d_a0;
              }
              _stack.emplace_back(_Call1{d_a1.get(), *(d_a10), max_val});
              _stack.emplace_back(_Enter{d_a2.get(), *(d_a20)});
            }
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s2});
          _stack.emplace_back(_Enter{_f._s0, _f._s1});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = ltree::lnode(_f._s1, _result, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, ltree, T1, ltree, T1> F1>
    T1 ltree_rec(F0 &&f, F1 &&f0) const {
      const ltree *_self = this;

      struct _Enter {
        const ltree *_self;
      };

      struct _Call1 {
        ltree *_s0;
        ltree _s1;
        ltree _s2;
        unsigned int _s3;
      };

      struct _Call2 {
        T1 _s0;
        ltree _s1;
        ltree _s2;
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
          auto _f = std::move(std::get<_Enter>(_frame));
          const ltree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename ltree::LLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename ltree::LLeaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename ltree::LNode>(_sv.v());
            _stack.emplace_back(_Call1{d_a1.get(), *(d_a2), *(d_a1), d_a0});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s3, _f._s2, _result, _f._s1, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, ltree, T1, ltree, T1> F1>
    T1 ltree_rect(F0 &&f, F1 &&f0) const {
      const ltree *_self = this;

      struct _Enter {
        const ltree *_self;
      };

      struct _Call1 {
        ltree *_s0;
        ltree _s1;
        ltree _s2;
        unsigned int _s3;
      };

      struct _Call2 {
        T1 _s0;
        ltree _s1;
        ltree _s2;
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
          auto _f = std::move(std::get<_Enter>(_frame));
          const ltree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename ltree::LLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename ltree::LLeaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename ltree::LNode>(_sv.v());
            _stack.emplace_back(_Call1{d_a1.get(), *(d_a2), *(d_a1), d_a0});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s3, _f._s2, _result, _f._s1, _f._s0);
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_STRUCTURES
