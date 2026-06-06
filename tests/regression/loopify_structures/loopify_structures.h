#ifndef INCLUDED_LOOPIFY_STRUCTURES
#define INCLUDED_LOOPIFY_STRUCTURES

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

/// Nested and complex data structures.
struct LoopifyStructures {
  /// Nested list: elements or nested lists.
  struct nested {
    // TYPES
    struct Elem {
      uint64_t a0;
    };

    struct NList {
      std::shared_ptr<List<nested>> a0;
    };

    using variant_t = std::variant<Elem, NList>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    nested() {}

    explicit nested(Elem _v) : v_(std::move(_v)) {}

    explicit nested(NList _v) : v_(std::move(_v)) {}

    static nested elem(uint64_t a0) { return nested(Elem{a0}); }

    static nested nlist(List<nested> a0) {
      return nested(NList{std::make_shared<List<nested>>(std::move(a0))});
    }

    // MANIPULATORS
    ~nested() {
      std::vector<std::shared_ptr<nested>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<NList>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            auto *_lp = _alt->a0.get();
            while (
                std::holds_alternative<typename List<nested>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<nested>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<nested>(std::move(_lc.a)));
              if (_lc.l) {
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
            _alt->a0.reset();
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// nested_flatten n flattens to a regular list.
    List<uint64_t> nested_flatten() const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        const auto &[a0] = std::get<typename nested::Elem>(this->v());
        return List<uint64_t>::cons(a0, List<uint64_t>::nil());
      } else {
        const auto &[a0] = std::get<typename nested::NList>(this->v());
        return flatten_nested_list_fuel(UINT64_C(1000), *a0);
      }
    }

    /// nested_depth n computes maximum nesting depth.
    uint64_t nested_depth() const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0] = std::get<typename nested::NList>(this->v());
        return (depth_nested_list_fuel(UINT64_C(1000), *a0) + 1);
      }
    }

    /// nested_sum n sums all elements in a nested structure.
    uint64_t nested_sum() const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        const auto &[a0] = std::get<typename nested::Elem>(this->v());
        return a0;
      } else {
        const auto &[a0] = std::get<typename nested::NList>(this->v());
        return sum_nested_list_fuel(UINT64_C(1000), *a0);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, List<nested> &>
    T1 nested_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        const auto &[a0] = std::get<typename nested::Elem>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename nested::NList>(this->v());
        return f0(*a0);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, List<nested> &>
    T1 nested_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename nested::Elem>(this->v())) {
        const auto &[a0] = std::get<typename nested::Elem>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename nested::NList>(this->v());
        return f0(*a0);
      }
    }
  };

  /// Helper: sum all elements in a list of nested structures.
  /// Handles both tree and list levels in one function for full loopification.
  static uint64_t sum_nested_list_fuel(uint64_t fuel, const List<nested> &l);
  /// Helper: compute max depth among a list of nested structures.
  static uint64_t depth_nested_list_fuel(uint64_t fuel, const List<nested> &l);
  /// Helper: flatten a list of nested structures to a flat list of nats.
  static List<uint64_t> flatten_nested_list_fuel(uint64_t fuel,
                                                 const List<nested> &l);

  /// Quadtree: leaf or 4-way branch.
  struct quadtree {
    // TYPES
    struct QLeaf {
      uint64_t a0;
    };

    struct Quad {
      std::shared_ptr<quadtree> a0;
      std::shared_ptr<quadtree> a1;
      std::shared_ptr<quadtree> a2;
      std::shared_ptr<quadtree> a3;
    };

    using variant_t = std::variant<QLeaf, Quad>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    quadtree() {}

    explicit quadtree(QLeaf _v) : v_(std::move(_v)) {}

    explicit quadtree(Quad _v) : v_(std::move(_v)) {}

    static quadtree qleaf(uint64_t a0) { return quadtree(QLeaf{a0}); }

    static quadtree quad(quadtree a0, quadtree a1, quadtree a2, quadtree a3) {
      return quadtree(Quad{std::make_shared<quadtree>(std::move(a0)),
                           std::make_shared<quadtree>(std::move(a1)),
                           std::make_shared<quadtree>(std::move(a2)),
                           std::make_shared<quadtree>(std::move(a3))});
    }

    // MANIPULATORS
    ~quadtree() {
      std::vector<std::shared_ptr<quadtree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Quad>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
          if (_alt->a3) {
            _stack.push_back(std::move(_alt->a3));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// quad_map f t applies function to all leaves.
    template <typename F0>
      requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
    quadtree quad_map(F0 &&f) const {
      if (std::holds_alternative<typename quadtree::QLeaf>(this->v())) {
        const auto &[a0] = std::get<typename quadtree::QLeaf>(this->v());
        return quadtree::qleaf(f(a0));
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename quadtree::Quad>(this->v());
        return quadtree::quad(a0->quad_map(f), a1->quad_map(f), a2->quad_map(f),
                              a3->quad_map(f));
      }
    }

    /// quad_depth t computes quadtree depth.
    uint64_t quad_depth() const {
      if (std::holds_alternative<typename quadtree::QLeaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename quadtree::Quad>(this->v());
        uint64_t d1 = a0->quad_depth();
        uint64_t d2 = a1->quad_depth();
        uint64_t d3 = a2->quad_depth();
        uint64_t d4 = a3->quad_depth();
        return ([&]() -> uint64_t {
          if ((d1 <= d2 ? d2 : d1) <= (d3 <= d4 ? d4 : d3)) {
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

    /// quad_sum t sums all values in quadtree.
    uint64_t quad_sum() const {
      if (std::holds_alternative<typename quadtree::QLeaf>(this->v())) {
        const auto &[a0] = std::get<typename quadtree::QLeaf>(this->v());
        return a0;
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename quadtree::Quad>(this->v());
        return (a0->quad_sum() +
                (a1->quad_sum() + (a2->quad_sum() + a3->quad_sum())));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename quadtree::QLeaf>(this->v())) {
        const auto &[a0] = std::get<typename quadtree::QLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename quadtree::Quad>(this->v());
        return f0(*a0, a0->template quadtree_rec<T1>(f, f0), *a1,
                  a1->template quadtree_rec<T1>(f, f0), *a2,
                  a2->template quadtree_rec<T1>(f, f0), *a3,
                  a3->template quadtree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename quadtree::QLeaf>(this->v())) {
        const auto &[a0] = std::get<typename quadtree::QLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename quadtree::Quad>(this->v());
        return f0(*a0, a0->template quadtree_rect<T1>(f, f0), *a1,
                  a1->template quadtree_rect<T1>(f, f0), *a2,
                  a2->template quadtree_rect<T1>(f, f0), *a3,
                  a3->template quadtree_rect<T1>(f, f0));
      }
    }
  };

  /// find_opt p l finds first element satisfying predicate, returns option.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static std::optional<uint64_t> find_opt(F0 &&p, const List<uint64_t> &l) {
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return std::optional<uint64_t>();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          return std::make_optional<uint64_t>(a0);
        } else {
          _loop_l = a1.get();
        }
      }
    }
  }

  /// map_opt f l maps option-returning function and filters out Nones.
  template <typename F0>
    requires std::is_invocable_r_v<std::optional<uint64_t>, F0 &, uint64_t &>
  static List<uint64_t>
  map_opt(F0 &&f,
          const List<uint64_t> &l) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Resume_y: saves [y], resumes after recursive call with _result.
    struct _Resume_y {
      uint64_t y;
    };

    using _Frame = std::variant<_Enter, _Resume_y>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified map_opt: _Enter -> _Resume_y.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto _cs = f(a0);
          if (_cs.has_value()) {
            const uint64_t &y = *_cs;
            _stack.emplace_back(_Resume_y{y});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_y>(_frame));
        _result = List<uint64_t>::cons(_f.y, std::move(_result));
      }
    }
    return _result;
  }

  /// filter_map p f l filters and maps in one pass.
  template <typename F0, typename F1>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static List<uint64_t>
  filter_map(F0 &&p, F1 &&f,
             const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Resume1: saves [a0], resumes after recursive call with _result.
    struct _Resume1 {
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified filter_map: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(_Resume1{f(a0)});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = List<uint64_t>::cons(_f.a0, std::move(_result));
      }
    }
    return _result;
  }

  /// find_first_some l finds first Some value in list of options.
  static std::optional<uint64_t>
  find_first_some(const List<std::optional<uint64_t>> &l);

  /// Tree type with values in leaves.
  struct ltree {
    // TYPES
    struct LLeaf {
      uint64_t a0;
    };

    struct LNode {
      uint64_t a0;
      std::shared_ptr<ltree> a1;
      std::shared_ptr<ltree> a2;
    };

    using variant_t = std::variant<LLeaf, LNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ltree() {}

    explicit ltree(LLeaf _v) : v_(std::move(_v)) {}

    explicit ltree(LNode _v) : v_(std::move(_v)) {}

    static ltree lleaf(uint64_t a0) { return ltree(LLeaf{a0}); }

    static ltree lnode(uint64_t a0, ltree a1, ltree a2) {
      return ltree(LNode{a0, std::make_shared<ltree>(std::move(a1)),
                         std::make_shared<ltree>(std::move(a2))});
    }

    // MANIPULATORS
    ~ltree() {
      std::vector<std::shared_ptr<ltree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<LNode>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// ltree_max t1 t2 element-wise max of two leaf-trees.
    ltree ltree_max(ltree t2) const {
      if (std::holds_alternative<typename ltree::LLeaf>(this->v())) {
        auto &[a0] = std::get<typename ltree::LLeaf>(this->v());
        if (std::holds_alternative<typename ltree::LLeaf>(t2.v_mut())) {
          auto &[a00] = std::get<typename ltree::LLeaf>(t2.v_mut());
          return ltree::lleaf((a0 <= a00 ? std::move(a00) : std::move(a0)));
        } else {
          return t2;
        }
      } else {
        auto &[a0, a1, a2] = std::get<typename ltree::LNode>(this->v());
        if (std::holds_alternative<typename ltree::LLeaf>(t2.v_mut())) {
          return *this;
        } else {
          auto &[a00, a10, a20] = std::get<typename ltree::LNode>(t2.v_mut());
          uint64_t max_val;
          if (a0 <= a00) {
            max_val = a00;
          } else {
            max_val = a0;
          }
          return ltree::lnode(max_val, a1->ltree_max(*a10),
                              a2->ltree_max(*a20));
        }
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &, ltree &, T1 &,
                                     ltree &, T1 &>
    T1 ltree_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename ltree::LLeaf>(this->v())) {
        const auto &[a0] = std::get<typename ltree::LLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename ltree::LNode>(this->v());
        return f0(a0, *a1, a1->template ltree_rec<T1>(f, f0), *a2,
                  a2->template ltree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &, ltree &, T1 &,
                                     ltree &, T1 &>
    T1 ltree_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename ltree::LLeaf>(this->v())) {
        const auto &[a0] = std::get<typename ltree::LLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename ltree::LNode>(this->v());
        return f0(a0, *a1, a1->template ltree_rect<T1>(f, f0), *a2,
                  a2->template ltree_rect<T1>(f, f0));
      }
    }
  };
};

#endif // INCLUDED_LOOPIFY_STRUCTURES
