#ifndef INCLUDED_LOOPIFY_TREE_VARIANTS
#define INCLUDED_LOOPIFY_TREE_VARIANTS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct LoopifyTreeVariants {
  struct ternary {
    // TYPES
    struct TLeaf {};

    struct TNode {
      std::unique_ptr<ternary> d_a0;
      unsigned int d_a1;
      std::unique_ptr<ternary> d_a2;
      std::unique_ptr<ternary> d_a3;
    };

    using variant_t = std::variant<TLeaf, TNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    ternary() {}

    explicit ternary(TLeaf _v) : d_v_(_v) {}

    explicit ternary(TNode _v) : d_v_(std::move(_v)) {}

    ternary(const ternary &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    ternary(ternary &&_other) : d_v_(std::move(_other.d_v_)) {}

    ternary &operator=(const ternary &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    ternary &operator=(ternary &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    ternary clone() const {
      ternary _out{};

      struct _CloneFrame {
        const ternary *_src;
        ternary *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const ternary *_src = _frame._src;
        ternary *_dst = _frame._dst;
        if (std::holds_alternative<TLeaf>(_src->v())) {
          _dst->d_v_ = TLeaf();
        } else {
          const auto &_alt = std::get<TNode>(_src->v());
          _dst->d_v_ = TNode(_alt.d_a0 ? std::make_unique<ternary>() : nullptr,
                             _alt.d_a1,
                             _alt.d_a2 ? std::make_unique<ternary>() : nullptr,
                             _alt.d_a3 ? std::make_unique<ternary>() : nullptr);
          auto &_dst_alt = std::get<TNode>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
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
    static ternary tleaf() { return ternary(TLeaf()); }

    static ternary tnode(ternary a0, unsigned int a1, ternary a2, ternary a3) {
      return ternary(TNode(std::make_unique<ternary>(std::move(a0)),
                           std::move(a1),
                           std::make_unique<ternary>(std::move(a2)),
                           std::make_unique<ternary>(std::move(a3))));
    }

    // MANIPULATORS
    ~ternary() {
      std::vector<std::unique_ptr<ternary>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](ternary &_node) {
        if (std::holds_alternative<TNode>(_node.d_v_)) {
          auto &_alt = std::get<TNode>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
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

    unsigned int ternary_count() const {
      const ternary *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ternary *_self;
      };

      /// _After_TNode: saves [_s0, _s1, _s2], dispatches next recursive call.
      struct _After_TNode {
        const ternary *_s0;
        const ternary *_s1;
        decltype(1u) _s2;
      };

      /// _After_TNode_1: saves [_result, _s1, _s2], dispatches next recursive
      /// call.
      struct _After_TNode_1 {
        unsigned int _result;
        const ternary *_s1;
        decltype(1u) _s2;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        unsigned int _result_0;
        unsigned int _result_1;
        decltype(1u) _s2;
      };

      using _Frame =
          std::variant<_Enter, _After_TNode, _After_TNode_1, _Combine_TNode>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified ternary_count: _Enter -> _After_TNode -> _After_TNode_1 ->
      /// _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(_After_TNode(d_a2.get(), d_a0.get(), 1u));
            _stack.emplace_back(_Enter(d_a3.get()));
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(_After_TNode_1(_result, _f._s1, _f._s2));
          _stack.emplace_back(_Enter(_f._s0));
        } else if (std::holds_alternative<_After_TNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_TNode_1>(_frame));
          _stack.emplace_back(_Combine_TNode(_f._result, _result, _f._s2));
          _stack.emplace_back(_Enter(_f._s1));
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result = (((_f._s2 + _result) + _f._result_1) + _f._result_0);
        }
      }
      return _result;
    }

    unsigned int ternary_sum() const {
      const ternary *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ternary *_self;
      };

      /// _After_TNode: saves [_s0, _s1, d_a1], dispatches next recursive call.
      struct _After_TNode {
        const ternary *_s0;
        const ternary *_s1;
        unsigned int d_a1;
      };

      /// _After_TNode_1: saves [_result, _s1, d_a1], dispatches next recursive
      /// call.
      struct _After_TNode_1 {
        unsigned int _result;
        const ternary *_s1;
        unsigned int d_a1;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        unsigned int _result_0;
        unsigned int _result_1;
        unsigned int d_a1;
      };

      using _Frame =
          std::variant<_Enter, _After_TNode, _After_TNode_1, _Combine_TNode>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified ternary_sum: _Enter -> _After_TNode -> _After_TNode_1 ->
      /// _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(_After_TNode(d_a2.get(), d_a0.get(), d_a1));
            _stack.emplace_back(_Enter(d_a3.get()));
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(_After_TNode_1(_result, _f._s1, _f.d_a1));
          _stack.emplace_back(_Enter(_f._s0));
        } else if (std::holds_alternative<_After_TNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_TNode_1>(_frame));
          _stack.emplace_back(_Combine_TNode(_f._result, _result, _f.d_a1));
          _stack.emplace_back(_Enter(_f._s1));
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result = (((_result + _f.d_a1) + _f._result_1) + _f._result_0);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ternary &, T1 &, unsigned int &,
                                     ternary &, T1 &, ternary &, T1 &>
    T1 ternary_rec(const T1 f, F1 &&f0) const {
      const ternary *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ternary *_self;
      };

      /// _After_TNode: saves [_s0, _s1, d_a3, d_a2, d_a1, d_a0], dispatches
      /// next recursive call.
      struct _After_TNode {
        const ternary *_s0;
        const ternary *_s1;
        ternary d_a3;
        ternary d_a2;
        unsigned int d_a1;
        ternary d_a0;
      };

      /// _After_TNode_1: saves [_result, _s1, d_a3, d_a2, d_a1, d_a0],
      /// dispatches next recursive call.
      struct _After_TNode_1 {
        T1 _result;
        const ternary *_s1;
        ternary d_a3;
        ternary d_a2;
        unsigned int d_a1;
        ternary d_a0;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        T1 _result_0;
        T1 _result_1;
        ternary d_a3;
        ternary d_a2;
        unsigned int d_a1;
        ternary d_a0;
      };

      using _Frame =
          std::variant<_Enter, _After_TNode, _After_TNode_1, _Combine_TNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified ternary_rec: _Enter -> _After_TNode -> _After_TNode_1 ->
      /// _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(_After_TNode(d_a2.get(), d_a0.get(), *(d_a3),
                                             *(d_a2), d_a1, *(d_a0)));
            _stack.emplace_back(_Enter(d_a3.get()));
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(
              _After_TNode_1(_result, _f._s1, std::move(_f.d_a3),
                             std::move(_f.d_a2), _f.d_a1, std::move(_f.d_a0)));
          _stack.emplace_back(_Enter(_f._s0));
        } else if (std::holds_alternative<_After_TNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_TNode_1>(_frame));
          _stack.emplace_back(
              _Combine_TNode(_f._result, _result, std::move(_f.d_a3),
                             std::move(_f.d_a2), _f.d_a1, std::move(_f.d_a0)));
          _stack.emplace_back(_Enter(_f._s1));
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f.d_a2, _f._result_1,
                       _f.d_a3, _f._result_0);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ternary &, T1 &, unsigned int &,
                                     ternary &, T1 &, ternary &, T1 &>
    T1 ternary_rect(const T1 f, F1 &&f0) const {
      const ternary *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ternary *_self;
      };

      /// _After_TNode: saves [_s0, _s1, d_a3, d_a2, d_a1, d_a0], dispatches
      /// next recursive call.
      struct _After_TNode {
        const ternary *_s0;
        const ternary *_s1;
        ternary d_a3;
        ternary d_a2;
        unsigned int d_a1;
        ternary d_a0;
      };

      /// _After_TNode_1: saves [_result, _s1, d_a3, d_a2, d_a1, d_a0],
      /// dispatches next recursive call.
      struct _After_TNode_1 {
        T1 _result;
        const ternary *_s1;
        ternary d_a3;
        ternary d_a2;
        unsigned int d_a1;
        ternary d_a0;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        T1 _result_0;
        T1 _result_1;
        ternary d_a3;
        ternary d_a2;
        unsigned int d_a1;
        ternary d_a0;
      };

      using _Frame =
          std::variant<_Enter, _After_TNode, _After_TNode_1, _Combine_TNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified ternary_rect: _Enter -> _After_TNode -> _After_TNode_1 ->
      /// _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(_After_TNode(d_a2.get(), d_a0.get(), *(d_a3),
                                             *(d_a2), d_a1, *(d_a0)));
            _stack.emplace_back(_Enter(d_a3.get()));
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(
              _After_TNode_1(_result, _f._s1, std::move(_f.d_a3),
                             std::move(_f.d_a2), _f.d_a1, std::move(_f.d_a0)));
          _stack.emplace_back(_Enter(_f._s0));
        } else if (std::holds_alternative<_After_TNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_TNode_1>(_frame));
          _stack.emplace_back(
              _Combine_TNode(_f._result, _result, std::move(_f.d_a3),
                             std::move(_f.d_a2), _f.d_a1, std::move(_f.d_a0)));
          _stack.emplace_back(_Enter(_f._s1));
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f.d_a2, _f._result_1,
                       _f.d_a3, _f._result_0);
        }
      }
      return _result;
    }
  };

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
          _result = (((_result + _f._result_2) + _f._result_1) + _f._result_0);
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

  struct leaf_tree {
    // TYPES
    struct LLeaf {
      unsigned int d_a0;
    };

    struct LNode {
      std::unique_ptr<leaf_tree> d_a0;
      std::unique_ptr<leaf_tree> d_a1;
    };

    using variant_t = std::variant<LLeaf, LNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    leaf_tree() {}

    explicit leaf_tree(LLeaf _v) : d_v_(std::move(_v)) {}

    explicit leaf_tree(LNode _v) : d_v_(std::move(_v)) {}

    leaf_tree(const leaf_tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    leaf_tree(leaf_tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    leaf_tree &operator=(const leaf_tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    leaf_tree &operator=(leaf_tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    leaf_tree clone() const {
      leaf_tree _out{};

      struct _CloneFrame {
        const leaf_tree *_src;
        leaf_tree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const leaf_tree *_src = _frame._src;
        leaf_tree *_dst = _frame._dst;
        if (std::holds_alternative<LLeaf>(_src->v())) {
          const auto &_alt = std::get<LLeaf>(_src->v());
          _dst->d_v_ = LLeaf(_alt.d_a0);
        } else {
          const auto &_alt = std::get<LNode>(_src->v());
          _dst->d_v_ =
              LNode(_alt.d_a0 ? std::make_unique<leaf_tree>() : nullptr,
                    _alt.d_a1 ? std::make_unique<leaf_tree>() : nullptr);
          auto &_dst_alt = std::get<LNode>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static leaf_tree lleaf(unsigned int a0) {
      return leaf_tree(LLeaf(std::move(a0)));
    }

    static leaf_tree lnode(leaf_tree a0, leaf_tree a1) {
      return leaf_tree(LNode(std::make_unique<leaf_tree>(std::move(a0)),
                             std::make_unique<leaf_tree>(std::move(a1))));
    }

    // MANIPULATORS
    ~leaf_tree() {
      std::vector<std::unique_ptr<leaf_tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](leaf_tree &_node) {
        if (std::holds_alternative<LNode>(_node.d_v_)) {
          auto &_alt = std::get<LNode>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
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

    unsigned int leaf_tree_max() const {
      const leaf_tree *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename leaf_tree::LLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<typename leaf_tree::LLeaf>(_sv.v());
        return d_a0;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename leaf_tree::LNode>(_sv.v());
        unsigned int lmax = (*(d_a0)).leaf_tree_max();
        unsigned int rmax = (*(d_a1)).leaf_tree_max();
        if (lmax < rmax) {
          return rmax;
        } else {
          return lmax;
        }
      }
    }

    unsigned int leaf_tree_sum() const {
      const leaf_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const leaf_tree *_self;
      };

      /// _After_LNode: saves [_s0], dispatches next recursive call.
      struct _After_LNode {
        leaf_tree *_s0;
      };

      /// _Combine_LNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LNode {
        unsigned int _result;
      };

      using _Frame = std::variant<_Enter, _After_LNode, _Combine_LNode>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified leaf_tree_sum: _Enter -> _After_LNode -> _Combine_LNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const leaf_tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename leaf_tree::LLeaf>(_sv.v());
            _result = d_a0;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename leaf_tree::LNode>(_sv.v());
            _stack.emplace_back(_After_LNode(d_a0.get()));
            _stack.emplace_back(_Enter(d_a1.get()));
          }
        } else if (std::holds_alternative<_After_LNode>(_frame)) {
          auto _f = std::move(std::get<_After_LNode>(_frame));
          _stack.emplace_back(_Combine_LNode(_result));
          _stack.emplace_back(_Enter(_f._s0));
        } else {
          auto _f = std::move(std::get<_Combine_LNode>(_frame));
          _result = (_result + _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, leaf_tree &, T1 &, leaf_tree &,
                                     T1 &>
    T1 leaf_tree_rec(F0 &&f, F1 &&f0) const {
      const leaf_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const leaf_tree *_self;
      };

      /// _After_LNode: saves [_s0, d_a1, d_a0], dispatches next recursive call.
      struct _After_LNode {
        leaf_tree *_s0;
        leaf_tree d_a1;
        leaf_tree d_a0;
      };

      /// _Combine_LNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LNode {
        T1 _result;
        leaf_tree d_a1;
        leaf_tree d_a0;
      };

      using _Frame = std::variant<_Enter, _After_LNode, _Combine_LNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified leaf_tree_rec: _Enter -> _After_LNode -> _Combine_LNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const leaf_tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename leaf_tree::LLeaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename leaf_tree::LNode>(_sv.v());
            _stack.emplace_back(_After_LNode(d_a0.get(), *(d_a1), *(d_a0)));
            _stack.emplace_back(_Enter(d_a1.get()));
          }
        } else if (std::holds_alternative<_After_LNode>(_frame)) {
          auto _f = std::move(std::get<_After_LNode>(_frame));
          _stack.emplace_back(
              _Combine_LNode(_result, std::move(_f.d_a1), std::move(_f.d_a0)));
          _stack.emplace_back(_Enter(_f._s0));
        } else {
          auto _f = std::move(std::get<_Combine_LNode>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, leaf_tree &, T1 &, leaf_tree &,
                                     T1 &>
    T1 leaf_tree_rect(F0 &&f, F1 &&f0) const {
      const leaf_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const leaf_tree *_self;
      };

      /// _After_LNode: saves [_s0, d_a1, d_a0], dispatches next recursive call.
      struct _After_LNode {
        leaf_tree *_s0;
        leaf_tree d_a1;
        leaf_tree d_a0;
      };

      /// _Combine_LNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LNode {
        T1 _result;
        leaf_tree d_a1;
        leaf_tree d_a0;
      };

      using _Frame = std::variant<_Enter, _After_LNode, _Combine_LNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter(_self));
      /// Loopified leaf_tree_rect: _Enter -> _After_LNode -> _Combine_LNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const leaf_tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename leaf_tree::LLeaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename leaf_tree::LNode>(_sv.v());
            _stack.emplace_back(_After_LNode(d_a0.get(), *(d_a1), *(d_a0)));
            _stack.emplace_back(_Enter(d_a1.get()));
          }
        } else if (std::holds_alternative<_After_LNode>(_frame)) {
          auto _f = std::move(std::get<_After_LNode>(_frame));
          _stack.emplace_back(
              _Combine_LNode(_result, std::move(_f.d_a1), std::move(_f.d_a0)));
          _stack.emplace_back(_Enter(_f._s0));
        } else {
          auto _f = std::move(std::get<_Combine_LNode>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f._result);
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_TREE_VARIANTS
