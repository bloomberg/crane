#ifndef INCLUDED_LOOPIFY_STRUCTURES
#define INCLUDED_LOOPIFY_STRUCTURES

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

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

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil();
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons(_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr);
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->d_v_ = Nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->d_v_ =
          Cons(t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr);
    }
  }

  static List<t_A> nil() { return List(Nil()); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons(std::move(a0), std::make_unique<List<t_A>>(std::move(a1))));
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
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

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }

  List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    List<t_A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(std::move(_loop_m));
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
      std::unique_ptr<List<nested>> d_a0;
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

    nested &operator=(const nested &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    nested &operator=(nested &&_other) {
      d_v_ = std::move(_other.d_v_);
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
          _dst->d_v_ = Elem(_alt.d_a0);
        } else {
          const auto &_alt = std::get<NList>(_src->v());
          _dst->d_v_ =
              NList(_alt.d_a0 ? std::make_unique<List<nested>>() : nullptr);
          auto &_dst_alt = std::get<NList>(_dst->d_v_);
          [&] {
            if (_alt.d_a0) {
              const List<nested> *_lsrc = _alt.d_a0.get();
              List<nested> *_ldst = _dst_alt.d_a0.get();
              while (std::holds_alternative<typename List<nested>::Cons>(
                  _lsrc->v())) {
                const auto &_lsrc_c =
                    std::get<typename List<nested>::Cons>(_lsrc->v());
                _ldst->v_mut() = typename List<nested>::Cons{
                    nested{},
                    _lsrc_c.d_a1 ? std::make_unique<List<nested>>() : nullptr};
                auto &_ldst_c =
                    std::get<typename List<nested>::Cons>(_ldst->v_mut());
                _stack.push_back({&_lsrc_c.d_a0, &_ldst_c.d_a0});
                if (_lsrc_c.d_a1) {
                  _lsrc = _lsrc_c.d_a1.get();
                  _ldst = _ldst_c.d_a1.get();
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
    static nested elem(unsigned int a0) { return nested(Elem(std::move(a0))); }

    static nested nlist(List<nested> a0) {
      return nested(NList(std::make_unique<List<nested>>(std::move(a0))));
    }

    // MANIPULATORS
    ~nested() {
      std::vector<std::unique_ptr<nested>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](nested &_node) {
        if (std::holds_alternative<NList>(_node.d_v_)) {
          auto &_alt = std::get<NList>(_node.d_v_);
          if (_alt.d_a0) {
            auto *_lp = _alt.d_a0.get();
            while (
                std::holds_alternative<typename List<nested>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<nested>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_unique<nested>(std::move(_lc.d_a0)));
              if (_lc.d_a1) {
                _lp = _lc.d_a1.get();
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    /// nested_flatten n flattens to a regular list.
    List<unsigned int> nested_flatten() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename nested::Elem>(_sv.v())) {
        const auto &[d_a0] = std::get<typename nested::Elem>(_sv.v());
        return List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
      } else {
        const auto &[d_a0] = std::get<typename nested::NList>(_sv.v());
        return flatten_nested_list_fuel(1000u, *(d_a0));
      }
    }

    /// nested_depth n computes maximum nesting depth.
    unsigned int nested_depth() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename nested::Elem>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0] = std::get<typename nested::NList>(_sv.v());
        return (depth_nested_list_fuel(1000u, *(d_a0)) + 1);
      }
    }

    /// nested_sum n sums all elements in a nested structure.
    unsigned int nested_sum() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename nested::Elem>(_sv.v())) {
        const auto &[d_a0] = std::get<typename nested::Elem>(_sv.v());
        return d_a0;
      } else {
        const auto &[d_a0] = std::get<typename nested::NList>(_sv.v());
        return sum_nested_list_fuel(1000u, *(d_a0));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, List<nested> &>
    T1 nested_rec(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename nested::Elem>(_sv.v())) {
        const auto &[d_a0] = std::get<typename nested::Elem>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename nested::NList>(_sv.v());
        return f0(*(d_a0));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, List<nested> &>
    T1 nested_rect(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename nested::Elem>(_sv.v())) {
        const auto &[d_a0] = std::get<typename nested::Elem>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename nested::NList>(_sv.v());
        return f0(*(d_a0));
      }
    }
  };

  /// Helper: sum all elements in a list of nested structures.
  /// Handles both tree and list levels in one function for full loopification.
  static unsigned int sum_nested_list_fuel(const unsigned int fuel,
                                           const List<nested> &l);
  /// Helper: compute max depth among a list of nested structures.
  static unsigned int depth_nested_list_fuel(const unsigned int fuel,
                                             const List<nested> &l);
  /// Helper: flatten a list of nested structures to a flat list of nats.
  static List<unsigned int> flatten_nested_list_fuel(const unsigned int fuel,
                                                     const List<nested> &l);

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

    quadtree &operator=(const quadtree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    quadtree &operator=(quadtree &&_other) {
      d_v_ = std::move(_other.d_v_);
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
          _dst->d_v_ = QLeaf(_alt.d_a0);
        } else {
          const auto &_alt = std::get<Quad>(_src->v());
          _dst->d_v_ = Quad(_alt.d_a0 ? std::make_unique<quadtree>() : nullptr,
                            _alt.d_a1 ? std::make_unique<quadtree>() : nullptr,
                            _alt.d_a2 ? std::make_unique<quadtree>() : nullptr,
                            _alt.d_a3 ? std::make_unique<quadtree>() : nullptr);
          auto &_dst_alt = std::get<Quad>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
          if (_alt.d_a3) {
            _stack.push_back({_alt.d_a3.get(), _dst_alt.d_a3.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static quadtree qleaf(unsigned int a0) {
      return quadtree(QLeaf(std::move(a0)));
    }

    static quadtree quad(quadtree a0, quadtree a1, quadtree a2, quadtree a3) {
      return quadtree(Quad(std::make_unique<quadtree>(std::move(a0)),
                           std::make_unique<quadtree>(std::move(a1)),
                           std::make_unique<quadtree>(std::move(a2)),
                           std::make_unique<quadtree>(std::move(a3))));
    }

    // MANIPULATORS
    ~quadtree() {
      std::vector<std::unique_ptr<quadtree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](quadtree &_node) {
        if (std::holds_alternative<Quad>(_node.d_v_)) {
          auto &_alt = std::get<Quad>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
          }
          if (_alt.d_a3) {
            _stack.push_back(std::move(_alt.d_a3));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    /// quad_map f t applies function to all leaves.
    template <typename F0>
      requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
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
      _stack.emplace_back(_Enter(_self));
      /// Loopified quad_map: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
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
            _stack.emplace_back(
                _After_Quad(d_a2.get(), d_a1.get(), d_a0.get()));
            _stack.emplace_back(_Enter(d_a3.get()));
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(
              _After_Quad_1(std::move(_result), _f._s1, _f._s2));
          _stack.emplace_back(_Enter(_f._s0));
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(
              _After_Quad_2(std::move(_f._result), std::move(_result), _f._s2));
          _stack.emplace_back(_Enter(_f._s1));
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(_Combine_Quad(std::move(_f._result_0),
                                            std::move(_f._result_1),
                                            std::move(_result)));
          _stack.emplace_back(_Enter(_f._s2));
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result =
              quadtree::quad(_result, _f._result_2, _f._result_1, _f._result_0);
        }
      }
      return _result;
    }

    /// quad_depth t computes quadtree depth.
    unsigned int quad_depth() const {
      const quadtree *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3] =
            std::get<typename quadtree::Quad>(_sv.v());
        unsigned int d1 = (*(d_a0)).quad_depth();
        unsigned int d2 = (*(d_a1)).quad_depth();
        unsigned int d3 = (*(d_a2)).quad_depth();
        unsigned int d4 = (*(d_a3)).quad_depth();
        return ([&]() -> unsigned int {
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
    unsigned int quad_sum() const {
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
        unsigned int _result;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, _s2], dispatches next
      /// recursive call.
      struct _After_Quad_2 {
        unsigned int _result_0;
        unsigned int _result_1;
        const quadtree *_s2;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        unsigned int _result_0;
        unsigned int _result_1;
        unsigned int _result_2;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified quad_sum: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
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
            _stack.emplace_back(
                _After_Quad(d_a2.get(), d_a1.get(), d_a0.get()));
            _stack.emplace_back(_Enter(d_a3.get()));
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1(_result, _f._s1, _f._s2));
          _stack.emplace_back(_Enter(_f._s0));
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(_After_Quad_2(_f._result, _result, _f._s2));
          _stack.emplace_back(_Enter(_f._s1));
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(
              _Combine_Quad(_f._result_0, _f._result_1, _result));
          _stack.emplace_back(_Enter(_f._s2));
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = (_result + (_f._result_2 + (_f._result_1 + _f._result_0)));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rec(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [_s0, _s1, _s2, d_a3, d_a2, d_a1, d_a0], dispatches
      /// next recursive call.
      struct _After_Quad {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree d_a3;
        quadtree d_a2;
        quadtree d_a1;
        quadtree d_a0;
      };

      /// _After_Quad_1: saves [_result, _s1, _s2, d_a3, d_a2, d_a1, d_a0],
      /// dispatches next recursive call.
      struct _After_Quad_1 {
        T1 _result;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree d_a3;
        quadtree d_a2;
        quadtree d_a1;
        quadtree d_a0;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, _s2, d_a3, d_a2, d_a1,
      /// d_a0], dispatches next recursive call.
      struct _After_Quad_2 {
        T1 _result_0;
        T1 _result_1;
        const quadtree *_s2;
        quadtree d_a3;
        quadtree d_a2;
        quadtree d_a1;
        quadtree d_a0;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        T1 _result_0;
        T1 _result_1;
        T1 _result_2;
        quadtree d_a3;
        quadtree d_a2;
        quadtree d_a1;
        quadtree d_a0;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified quadtree_rec: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
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
            _stack.emplace_back(_After_Quad(d_a2.get(), d_a1.get(), d_a0.get(),
                                            *(d_a3), *(d_a2), *(d_a1),
                                            *(d_a0)));
            _stack.emplace_back(_Enter(d_a3.get()));
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1(
              _result, _f._s1, _f._s2, std::move(_f.d_a3), std::move(_f.d_a2),
              std::move(_f.d_a1), std::move(_f.d_a0)));
          _stack.emplace_back(_Enter(_f._s0));
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(_After_Quad_2(
              _f._result, _result, _f._s2, std::move(_f.d_a3),
              std::move(_f.d_a2), std::move(_f.d_a1), std::move(_f.d_a0)));
          _stack.emplace_back(_Enter(_f._s1));
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(_Combine_Quad(
              _f._result_0, _f._result_1, _result, std::move(_f.d_a3),
              std::move(_f.d_a2), std::move(_f.d_a1), std::move(_f.d_a0)));
          _stack.emplace_back(_Enter(_f._s2));
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f._result_2, _f.d_a2,
                       _f._result_1, _f.d_a3, _f._result_0);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rect(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [_s0, _s1, _s2, d_a3, d_a2, d_a1, d_a0], dispatches
      /// next recursive call.
      struct _After_Quad {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree d_a3;
        quadtree d_a2;
        quadtree d_a1;
        quadtree d_a0;
      };

      /// _After_Quad_1: saves [_result, _s1, _s2, d_a3, d_a2, d_a1, d_a0],
      /// dispatches next recursive call.
      struct _After_Quad_1 {
        T1 _result;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree d_a3;
        quadtree d_a2;
        quadtree d_a1;
        quadtree d_a0;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, _s2, d_a3, d_a2, d_a1,
      /// d_a0], dispatches next recursive call.
      struct _After_Quad_2 {
        T1 _result_0;
        T1 _result_1;
        const quadtree *_s2;
        quadtree d_a3;
        quadtree d_a2;
        quadtree d_a1;
        quadtree d_a0;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        T1 _result_0;
        T1 _result_1;
        T1 _result_2;
        quadtree d_a3;
        quadtree d_a2;
        quadtree d_a1;
        quadtree d_a0;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified quadtree_rect: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
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
            _stack.emplace_back(_After_Quad(d_a2.get(), d_a1.get(), d_a0.get(),
                                            *(d_a3), *(d_a2), *(d_a1),
                                            *(d_a0)));
            _stack.emplace_back(_Enter(d_a3.get()));
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1(
              _result, _f._s1, _f._s2, std::move(_f.d_a3), std::move(_f.d_a2),
              std::move(_f.d_a1), std::move(_f.d_a0)));
          _stack.emplace_back(_Enter(_f._s0));
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(_After_Quad_2(
              _f._result, _result, _f._s2, std::move(_f.d_a3),
              std::move(_f.d_a2), std::move(_f.d_a1), std::move(_f.d_a0)));
          _stack.emplace_back(_Enter(_f._s1));
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(_Combine_Quad(
              _f._result_0, _f._result_1, _result, std::move(_f.d_a3),
              std::move(_f.d_a2), std::move(_f.d_a1), std::move(_f.d_a0)));
          _stack.emplace_back(_Enter(_f._s2));
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f._result_2, _f.d_a2,
                       _f._result_1, _f.d_a3, _f._result_0);
        }
      }
      return _result;
    }
  };

  /// find_opt p l finds first element satisfying predicate, returns option.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static std::optional<unsigned int> find_opt(F0 &&p,
                                              const List<unsigned int> &l) {
    std::optional<unsigned int> _result;
    const List<unsigned int> *_loop_l = &l;
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
          _loop_l = d_a1.get();
        }
      }
    }
    return _result;
  }

  /// map_opt f l maps option-returning function and filters out Nones.
  template <typename F0>
    requires std::is_invocable_r_v<std::optional<unsigned int>, F0 &,
                                   unsigned int &>
  static List<unsigned int> map_opt(F0 &&f, const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      auto _cs = f(d_a0);
      if (_cs.has_value()) {
        const unsigned int &y = *_cs;
        return List<unsigned int>::cons(y, map_opt(f, *(d_a1)));
      } else {
        return map_opt(f, *(d_a1));
      }
    }
  } /// filter_map p f l filters and maps in one pass.

  template <typename F0, typename F1>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &> &&
             std::is_invocable_r_v<unsigned int, F1 &, unsigned int &>
  static List<unsigned int> filter_map(F0 &&p, F1 &&f,
                                       const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      if (p(d_a0)) {
        return List<unsigned int>::cons(f(d_a0), filter_map(p, f, *(d_a1)));
      } else {
        return filter_map(p, f, *(d_a1));
      }
    }
  }

  /// find_first_some l finds first Some value in list of options.
  static std::optional<unsigned int>
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

    ltree &operator=(const ltree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    ltree &operator=(ltree &&_other) {
      d_v_ = std::move(_other.d_v_);
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
          _dst->d_v_ = LLeaf(_alt.d_a0);
        } else {
          const auto &_alt = std::get<LNode>(_src->v());
          _dst->d_v_ =
              LNode(_alt.d_a0, _alt.d_a1 ? std::make_unique<ltree>() : nullptr,
                    _alt.d_a2 ? std::make_unique<ltree>() : nullptr);
          auto &_dst_alt = std::get<LNode>(_dst->d_v_);
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static ltree lleaf(unsigned int a0) { return ltree(LLeaf(std::move(a0))); }

    static ltree lnode(unsigned int a0, ltree a1, ltree a2) {
      return ltree(LNode(std::move(a0), std::make_unique<ltree>(std::move(a1)),
                         std::make_unique<ltree>(std::move(a2))));
    }

    // MANIPULATORS
    ~ltree() {
      std::vector<std::unique_ptr<ltree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](ltree &_node) {
        if (std::holds_alternative<LNode>(_node.d_v_)) {
          auto &_alt = std::get<LNode>(_node.d_v_);
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    /// ltree_max t1 t2 element-wise max of two leaf-trees.
    ltree ltree_max(ltree t2) const {
      const ltree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ltree *_self;
        ltree t2;
      };

      /// _After_LNode: saves [_s0, d_a10, max_val], dispatches next recursive
      /// call.
      struct _After_LNode {
        ltree *_s0;
        ltree d_a10;
        unsigned int max_val;
      };

      /// _Combine_LNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LNode {
        ltree _result;
        unsigned int max_val;
      };

      using _Frame = std::variant<_Enter, _After_LNode, _Combine_LNode>;
      ltree _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self, t2));
      /// Loopified ltree_max: _Enter -> _After_LNode -> _Combine_LNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ltree *_self = _f._self;
          ltree t2 = std::move(_f.t2);
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename ltree::LLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename ltree::LLeaf>(_sv.v());
            if (std::holds_alternative<typename ltree::LLeaf>(t2.v_mut())) {
              auto &[d_a00] = std::get<typename ltree::LLeaf>(t2.v_mut());
              _result = ltree::lleaf((d_a0 <= d_a00 ? d_a00 : d_a0));
            } else {
              _result = t2;
            }
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename ltree::LNode>(_sv.v());
            if (std::holds_alternative<typename ltree::LLeaf>(t2.v_mut())) {
              _result = *(_self);
            } else {
              auto &[d_a00, d_a10, d_a20] =
                  std::get<typename ltree::LNode>(t2.v_mut());
              unsigned int max_val;
              if (d_a0 <= d_a00) {
                max_val = d_a00;
              } else {
                max_val = d_a0;
              }
              _stack.emplace_back(_After_LNode(d_a1.get(), *(d_a10), max_val));
              _stack.emplace_back(_Enter(d_a2.get(), std::move(*(d_a20))));
            }
          }
        } else if (std::holds_alternative<_After_LNode>(_frame)) {
          auto _f = std::move(std::get<_After_LNode>(_frame));
          _stack.emplace_back(_Combine_LNode(std::move(_result), _f.max_val));
          _stack.emplace_back(_Enter(_f._s0, std::move(_f.d_a10)));
        } else {
          auto _f = std::move(std::get<_Combine_LNode>(_frame));
          _result = ltree::lnode(_f.max_val, _result, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, unsigned int &, ltree &, T1 &,
                                     ltree &, T1 &>
    T1 ltree_rec(F0 &&f, F1 &&f0) const {
      const ltree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ltree *_self;
      };

      /// _After_LNode: saves [_s0, d_a2, d_a1, d_a0], dispatches next recursive
      /// call.
      struct _After_LNode {
        ltree *_s0;
        ltree d_a2;
        ltree d_a1;
        unsigned int d_a0;
      };

      /// _Combine_LNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LNode {
        T1 _result;
        ltree d_a2;
        ltree d_a1;
        unsigned int d_a0;
      };

      using _Frame = std::variant<_Enter, _After_LNode, _Combine_LNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified ltree_rec: _Enter -> _After_LNode -> _Combine_LNode.
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
            _stack.emplace_back(
                _After_LNode(d_a1.get(), *(d_a2), *(d_a1), d_a0));
            _stack.emplace_back(_Enter(d_a2.get()));
          }
        } else if (std::holds_alternative<_After_LNode>(_frame)) {
          auto _f = std::move(std::get<_After_LNode>(_frame));
          _stack.emplace_back(_Combine_LNode(_result, std::move(_f.d_a2),
                                             std::move(_f.d_a1), _f.d_a0));
          _stack.emplace_back(_Enter(_f._s0));
        } else {
          auto _f = std::move(std::get<_Combine_LNode>(_frame));
          _result = f0(_f.d_a0, _f.d_a1, _result, _f.d_a2, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, unsigned int &, ltree &, T1 &,
                                     ltree &, T1 &>
    T1 ltree_rect(F0 &&f, F1 &&f0) const {
      const ltree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ltree *_self;
      };

      /// _After_LNode: saves [_s0, d_a2, d_a1, d_a0], dispatches next recursive
      /// call.
      struct _After_LNode {
        ltree *_s0;
        ltree d_a2;
        ltree d_a1;
        unsigned int d_a0;
      };

      /// _Combine_LNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LNode {
        T1 _result;
        ltree d_a2;
        ltree d_a1;
        unsigned int d_a0;
      };

      using _Frame = std::variant<_Enter, _After_LNode, _Combine_LNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified ltree_rect: _Enter -> _After_LNode -> _Combine_LNode.
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
            _stack.emplace_back(
                _After_LNode(d_a1.get(), *(d_a2), *(d_a1), d_a0));
            _stack.emplace_back(_Enter(d_a2.get()));
          }
        } else if (std::holds_alternative<_After_LNode>(_frame)) {
          auto _f = std::move(std::get<_After_LNode>(_frame));
          _stack.emplace_back(_Combine_LNode(_result, std::move(_f.d_a2),
                                             std::move(_f.d_a1), _f.d_a0));
          _stack.emplace_back(_Enter(_f._s0));
        } else {
          auto _f = std::move(std::get<_Combine_LNode>(_frame));
          _result = f0(_f.d_a0, _f.d_a1, _result, _f.d_a2, _f._result);
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_STRUCTURES
