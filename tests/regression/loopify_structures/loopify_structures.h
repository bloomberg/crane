#ifndef INCLUDED_LOOPIFY_STRUCTURES
#define INCLUDED_LOOPIFY_STRUCTURES

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
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    std::unique_ptr<List<A>> _head{};
    std::unique_ptr<List<A>> *_write = &_head;
    const List *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_unique<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_unique<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).a1;
        _loop_self = a1.get();
        continue;
      }
    }
    return std::move(*_head);
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
      std::unique_ptr<List<nested>> a0;
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

    nested(const nested &_other) : v_(std::move(_other.clone().v_)) {}

    nested(nested &&_other) noexcept : v_(std::move(_other.v_)) {}

    nested &operator=(const nested &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    nested &operator=(nested &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    nested clone() const {
      nested _out{};

      struct _CloneFrame {
        const nested *_src;
        nested *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const nested *_src = _frame._src;
        nested *_dst = _frame._dst;
        if (std::holds_alternative<Elem>(_src->v())) {
          const auto &_alt = std::get<Elem>(_src->v());
          _dst->v_ = Elem{_alt.a0};
        } else {
          const auto &_alt = std::get<NList>(_src->v());
          _dst->v_ =
              NList{_alt.a0 ? std::make_unique<List<nested>>() : nullptr};
          auto &_dst_alt = std::get<NList>(_dst->v_);
          [&] {
            if (_alt.a0) {
              const List<nested> *_lsrc = _alt.a0.get();
              List<nested> *_ldst = _dst_alt.a0.get();
              while (std::holds_alternative<typename List<nested>::Cons>(
                  _lsrc->v())) {
                const auto &_lsrc_c =
                    std::get<typename List<nested>::Cons>(_lsrc->v());
                _ldst->v_mut() = typename List<nested>::Cons{
                    nested{},
                    _lsrc_c.a1 ? std::make_unique<List<nested>>() : nullptr};
                auto &_ldst_c =
                    std::get<typename List<nested>::Cons>(_ldst->v_mut());
                _stack.push_back({&_lsrc_c.a0, &_ldst_c.a0});
                if (_lsrc_c.a1) {
                  _lsrc = _lsrc_c.a1.get();
                  _ldst = _ldst_c.a1.get();
                } else {
                  break;
                }
              }
              if (std::holds_alternative<typename List<nested>::Nil>(
                      _lsrc->v())) {
                _ldst->v_mut() = typename List<nested>::Nil{};
              }
            }
          }();
        }
      }
      return _out;
    }

    // CREATORS
    static nested elem(uint64_t a0) { return nested(Elem{a0}); }

    static nested nlist(List<nested> a0) {
      return nested(NList{std::make_unique<List<nested>>(std::move(a0))});
    }

    // MANIPULATORS
    ~nested() {
      std::vector<std::unique_ptr<nested>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](nested &_node) {
        if (std::holds_alternative<NList>(_node.v_)) {
          auto &_alt = std::get<NList>(_node.v_);
          if (_alt.a0) {
            auto *_lp = _alt.a0.get();
            while (
                std::holds_alternative<typename List<nested>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<nested>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_unique<nested>(std::move(_lc.a0)));
              if (_lc.a1) {
                _lp = _lc.a1.get();
              } else {
                break;
              }
            }
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
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
      std::unique_ptr<quadtree> a0;
      std::unique_ptr<quadtree> a1;
      std::unique_ptr<quadtree> a2;
      std::unique_ptr<quadtree> a3;
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

    quadtree(const quadtree &_other) : v_(std::move(_other.clone().v_)) {}

    quadtree(quadtree &&_other) noexcept : v_(std::move(_other.v_)) {}

    quadtree &operator=(const quadtree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    quadtree &operator=(quadtree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    quadtree clone() const {
      quadtree _out{};

      struct _CloneFrame {
        const quadtree *_src;
        quadtree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const quadtree *_src = _frame._src;
        quadtree *_dst = _frame._dst;
        if (std::holds_alternative<QLeaf>(_src->v())) {
          const auto &_alt = std::get<QLeaf>(_src->v());
          _dst->v_ = QLeaf{_alt.a0};
        } else {
          const auto &_alt = std::get<Quad>(_src->v());
          _dst->v_ = Quad{_alt.a0 ? std::make_unique<quadtree>() : nullptr,
                          _alt.a1 ? std::make_unique<quadtree>() : nullptr,
                          _alt.a2 ? std::make_unique<quadtree>() : nullptr,
                          _alt.a3 ? std::make_unique<quadtree>() : nullptr};
          auto &_dst_alt = std::get<Quad>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
          if (_alt.a3) {
            _stack.push_back({_alt.a3.get(), _dst_alt.a3.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static quadtree qleaf(uint64_t a0) { return quadtree(QLeaf{a0}); }

    static quadtree quad(quadtree a0, quadtree a1, quadtree a2, quadtree a3) {
      return quadtree(Quad{std::make_unique<quadtree>(std::move(a0)),
                           std::make_unique<quadtree>(std::move(a1)),
                           std::make_unique<quadtree>(std::move(a2)),
                           std::make_unique<quadtree>(std::move(a3))});
    }

    // MANIPULATORS
    ~quadtree() {
      std::vector<std::unique_ptr<quadtree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](quadtree &_node) {
        if (std::holds_alternative<Quad>(_node.v_)) {
          auto &_alt = std::get<Quad>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
          }
          if (_alt.a3) {
            _stack.push_back(std::move(_alt.a3));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
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
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [_s0, _s1, _s2], dispatches next recursive call.
      struct _After_Quad {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      /// _After_Quad_1: saves [_result, _s1, _s2], dispatches next recursive
      /// call.
      struct _After_Quad_1 {
        quadtree _result;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, _s2], dispatches next
      /// recursive call.
      struct _After_Quad_2 {
        quadtree _result_0;
        quadtree _result_1;
        const quadtree *_s2;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        quadtree _result_0;
        quadtree _result_1;
        quadtree _result_2;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      quadtree _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified quad_map: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = quadtree::qleaf(f(a0));
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_After_Quad{a2.get(), a1.get(), a0.get()});
            _stack.emplace_back(_Enter{a3.get()});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(
              _After_Quad_1{std::move(_result), _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(
              _After_Quad_2{std::move(_f._result), std::move(_result), _f._s2});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(_Combine_Quad{std::move(_f._result_0),
                                            std::move(_f._result_1),
                                            std::move(_result)});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result =
              quadtree::quad(_result, _f._result_2, _f._result_1, _f._result_0);
        }
      }
      return _result;
    }

    /// quad_depth t computes quadtree depth.
    uint64_t quad_depth() const {
      const quadtree *_self = this;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename quadtree::Quad>(_sv.v());
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
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [_s0, _s1, _s2], dispatches next recursive call.
      struct _After_Quad {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      /// _After_Quad_1: saves [_result, _s1, _s2], dispatches next recursive
      /// call.
      struct _After_Quad_1 {
        uint64_t _result;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, _s2], dispatches next
      /// recursive call.
      struct _After_Quad_2 {
        uint64_t _result_0;
        uint64_t _result_1;
        const quadtree *_s2;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        uint64_t _result_0;
        uint64_t _result_1;
        uint64_t _result_2;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified quad_sum: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_After_Quad{a2.get(), a1.get(), a0.get()});
            _stack.emplace_back(_Enter{a3.get()});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(_After_Quad_2{_f._result, _result, _f._s2});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(
              _Combine_Quad{_f._result_0, _f._result_1, _result});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = (_result + (_f._result_2 + (_f._result_1 + _f._result_0)));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rec(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [_s0, _s1, _s2, a3, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_Quad {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      /// _After_Quad_1: saves [_result, _s1, _s2, a3, a2, a1, a0], dispatches
      /// next recursive call.
      struct _After_Quad_1 {
        T1 _result;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, _s2, a3, a2, a1, a0],
      /// dispatches next recursive call.
      struct _After_Quad_2 {
        T1 _result_0;
        T1 _result_1;
        const quadtree *_s2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        T1 _result_0;
        T1 _result_1;
        T1 _result_2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified quadtree_rec: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(
                _After_Quad{a2.get(), a1.get(), a0.get(), *a3, *a2, *a1, *a0});
            _stack.emplace_back(_Enter{a3.get()});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{
              _result, _f._s1, _f._s2, std::move(_f.a3), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(_After_Quad_2{
              _f._result, _result, _f._s2, std::move(_f.a3), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(_Combine_Quad{
              _f._result_0, _f._result_1, _result, std::move(_f.a3),
              std::move(_f.a2), std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result_2, _f.a2, _f._result_1,
                       _f.a3, _f._result_0);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rect(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [_s0, _s1, _s2, a3, a2, a1, a0], dispatches next
      /// recursive call.
      struct _After_Quad {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      /// _After_Quad_1: saves [_result, _s1, _s2, a3, a2, a1, a0], dispatches
      /// next recursive call.
      struct _After_Quad_1 {
        T1 _result;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, _s2, a3, a2, a1, a0],
      /// dispatches next recursive call.
      struct _After_Quad_2 {
        T1 _result_0;
        T1 _result_1;
        const quadtree *_s2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        T1 _result_0;
        T1 _result_1;
        T1 _result_2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified quadtree_rect: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(
                _After_Quad{a2.get(), a1.get(), a0.get(), *a3, *a2, *a1, *a0});
            _stack.emplace_back(_Enter{a3.get()});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{
              _result, _f._s1, _f._s2, std::move(_f.a3), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(_After_Quad_2{
              _f._result, _result, _f._s2, std::move(_f.a3), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(_Combine_Quad{
              _f._result_0, _f._result_1, _result, std::move(_f.a3),
              std::move(_f.a2), std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result_2, _f.a2, _f._result_1,
                       _f.a3, _f._result_0);
        }
      }
      return _result;
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
  static List<uint64_t> map_opt(F0 &&f, const List<uint64_t> &l) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return List<uint64_t>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      auto _cs = f(a0);
      if (_cs.has_value()) {
        const uint64_t &y = *_cs;
        return List<uint64_t>::cons(y, map_opt(f, *a1));
      } else {
        return map_opt(f, *a1);
      }
    }
  } /// filter_map p f l filters and maps in one pass.

  template <typename F0, typename F1>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static List<uint64_t> filter_map(F0 &&p, F1 &&f, const List<uint64_t> &l) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return List<uint64_t>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      if (p(a0)) {
        return List<uint64_t>::cons(f(a0), filter_map(p, f, *a1));
      } else {
        return filter_map(p, f, *a1);
      }
    }
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
      std::unique_ptr<ltree> a1;
      std::unique_ptr<ltree> a2;
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

    ltree(const ltree &_other) : v_(std::move(_other.clone().v_)) {}

    ltree(ltree &&_other) noexcept : v_(std::move(_other.v_)) {}

    ltree &operator=(const ltree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    ltree &operator=(ltree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    ltree clone() const {
      ltree _out{};

      struct _CloneFrame {
        const ltree *_src;
        ltree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const ltree *_src = _frame._src;
        ltree *_dst = _frame._dst;
        if (std::holds_alternative<LLeaf>(_src->v())) {
          const auto &_alt = std::get<LLeaf>(_src->v());
          _dst->v_ = LLeaf{_alt.a0};
        } else {
          const auto &_alt = std::get<LNode>(_src->v());
          _dst->v_ =
              LNode{_alt.a0, _alt.a1 ? std::make_unique<ltree>() : nullptr,
                    _alt.a2 ? std::make_unique<ltree>() : nullptr};
          auto &_dst_alt = std::get<LNode>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static ltree lleaf(uint64_t a0) { return ltree(LLeaf{a0}); }

    static ltree lnode(uint64_t a0, ltree a1, ltree a2) {
      return ltree(LNode{a0, std::make_unique<ltree>(std::move(a1)),
                         std::make_unique<ltree>(std::move(a2))});
    }

    // MANIPULATORS
    ~ltree() {
      std::vector<std::unique_ptr<ltree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](ltree &_node) {
        if (std::holds_alternative<LNode>(_node.v_)) {
          auto &_alt = std::get<LNode>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// ltree_max t1 t2 element-wise max of two leaf-trees.
    ltree ltree_max(ltree t2) const {
      const ltree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ltree *_self;
        ltree t2;
      };

      /// _After_LNode: saves [_s0, a10, max_val], dispatches next recursive
      /// call.
      struct _After_LNode {
        ltree *_s0;
        ltree a10;
        uint64_t max_val;
      };

      /// _Combine_LNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LNode {
        ltree _result;
        uint64_t max_val;
      };

      using _Frame = std::variant<_Enter, _After_LNode, _Combine_LNode>;
      ltree _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self, t2});
      /// Loopified ltree_max: _Enter -> _After_LNode -> _Combine_LNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ltree *_self = _f._self;
          ltree t2 = std::move(_f.t2);
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ltree::LLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename ltree::LLeaf>(_sv.v());
            if (std::holds_alternative<typename ltree::LLeaf>(t2.v_mut())) {
              auto &[a00] = std::get<typename ltree::LLeaf>(t2.v_mut());
              _result =
                  ltree::lleaf((a0 <= a00 ? std::move(a00) : std::move(a0)));
            } else {
              _result = std::move(t2);
            }
          } else {
            const auto &[a0, a1, a2] = std::get<typename ltree::LNode>(_sv.v());
            if (std::holds_alternative<typename ltree::LLeaf>(t2.v_mut())) {
              _result = *_self;
            } else {
              auto &[a00, a10, a20] =
                  std::get<typename ltree::LNode>(t2.v_mut());
              uint64_t max_val;
              if (a0 <= a00) {
                max_val = a00;
              } else {
                max_val = a0;
              }
              _stack.emplace_back(_After_LNode{a1.get(), *a10, max_val});
              _stack.emplace_back(_Enter{a2.get(), std::move(*a20)});
            }
          }
        } else if (std::holds_alternative<_After_LNode>(_frame)) {
          auto _f = std::move(std::get<_After_LNode>(_frame));
          _stack.emplace_back(_Combine_LNode{std::move(_result), _f.max_val});
          _stack.emplace_back(_Enter{_f._s0, std::move(_f.a10)});
        } else {
          auto _f = std::move(std::get<_Combine_LNode>(_frame));
          _result = ltree::lnode(_f.max_val, _result, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &, ltree &, T1 &,
                                     ltree &, T1 &>
    T1 ltree_rec(F0 &&f, F1 &&f0) const {
      const ltree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ltree *_self;
      };

      /// _After_LNode: saves [_s0, a2, a1, a0], dispatches next recursive call.
      struct _After_LNode {
        ltree *_s0;
        ltree a2;
        ltree a1;
        uint64_t a0;
      };

      /// _Combine_LNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LNode {
        T1 _result;
        ltree a2;
        ltree a1;
        uint64_t a0;
      };

      using _Frame = std::variant<_Enter, _After_LNode, _Combine_LNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified ltree_rec: _Enter -> _After_LNode -> _Combine_LNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ltree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ltree::LLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename ltree::LLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename ltree::LNode>(_sv.v());
            _stack.emplace_back(_After_LNode{a1.get(), *a2, *a1, a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_LNode>(_frame)) {
          auto _f = std::move(std::get<_After_LNode>(_frame));
          _stack.emplace_back(_Combine_LNode{_result, std::move(_f.a2),
                                             std::move(_f.a1), _f.a0});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_LNode>(_frame));
          _result = f0(_f.a0, _f.a1, _result, _f.a2, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &, ltree &, T1 &,
                                     ltree &, T1 &>
    T1 ltree_rect(F0 &&f, F1 &&f0) const {
      const ltree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ltree *_self;
      };

      /// _After_LNode: saves [_s0, a2, a1, a0], dispatches next recursive call.
      struct _After_LNode {
        ltree *_s0;
        ltree a2;
        ltree a1;
        uint64_t a0;
      };

      /// _Combine_LNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LNode {
        T1 _result;
        ltree a2;
        ltree a1;
        uint64_t a0;
      };

      using _Frame = std::variant<_Enter, _After_LNode, _Combine_LNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified ltree_rect: _Enter -> _After_LNode -> _Combine_LNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ltree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ltree::LLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename ltree::LLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename ltree::LNode>(_sv.v());
            _stack.emplace_back(_After_LNode{a1.get(), *a2, *a1, a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_LNode>(_frame)) {
          auto _f = std::move(std::get<_After_LNode>(_frame));
          _stack.emplace_back(_Combine_LNode{_result, std::move(_f.a2),
                                             std::move(_f.a1), _f.a0});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_LNode>(_frame));
          _result = f0(_f.a0, _f.a1, _result, _f.a2, _f._result);
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_STRUCTURES
