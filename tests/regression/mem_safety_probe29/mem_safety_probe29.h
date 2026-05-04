#ifndef INCLUDED_MEM_SAFETY_PROBE29
#define INCLUDED_MEM_SAFETY_PROBE29

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe29 {
  /// An inner tree type — value type with recursive children.
  struct inner {
    // TYPES
    struct ILeaf {};

    struct INode {
      std::unique_ptr<inner> d_a0;
      unsigned int d_a1;
      std::unique_ptr<inner> d_a2;
    };

    using variant_t = std::variant<ILeaf, INode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    inner() {}

    explicit inner(ILeaf _v) : d_v_(_v) {}

    explicit inner(INode _v) : d_v_(std::move(_v)) {}

    inner(const inner &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    inner(inner &&_other) : d_v_(std::move(_other.d_v_)) {}

    inner &operator=(const inner &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    inner &operator=(inner &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    inner clone() const {
      inner _out{};

      struct _CloneFrame {
        const inner *_src;
        inner *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const inner *_src = _frame._src;
        inner *_dst = _frame._dst;
        if (std::holds_alternative<ILeaf>(_src->v())) {
          _dst->d_v_ = ILeaf{};
        } else {
          const auto &_alt = std::get<INode>(_src->v());
          _dst->d_v_ =
              INode{_alt.d_a0 ? std::make_unique<inner>() : nullptr, _alt.d_a1,
                    _alt.d_a2 ? std::make_unique<inner>() : nullptr};
          auto &_dst_alt = std::get<INode>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static inner ileaf() { return inner(ILeaf{}); }

    static inner inode(inner a0, unsigned int a1, inner a2) {
      return inner(INode{std::make_unique<inner>(std::move(a0)), std::move(a1),
                         std::make_unique<inner>(std::move(a2))});
    }

    // MANIPULATORS
    ~inner() {
      std::vector<std::unique_ptr<inner>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](inner &_node) {
        if (std::holds_alternative<INode>(_node.d_v_)) {
          auto &_alt = std::get<INode>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
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

    /// TEST 3: Transform outer tree — rebuild with modified inner values.
    inner double_inner() const {
      const inner *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const inner *_self;
      };

      /// _After_INode: saves [_s0, _s1], dispatches next recursive call.
      struct _After_INode {
        inner *_s0;
        unsigned int _s1;
      };

      /// _Combine_INode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_INode {
        inner _result;
        unsigned int _s1;
      };

      using _Frame = std::variant<_Enter, _After_INode, _Combine_INode>;
      inner _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified double_inner: _Enter -> _After_INode -> _Combine_INode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const inner *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename inner::ILeaf>(_sv.v())) {
            _result = inner::ileaf();
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename inner::INode>(_sv.v());
            _stack.emplace_back(_After_INode{d_a0.get(), (d_a1 * 2u)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_INode>(_frame)) {
          auto _f = std::move(std::get<_After_INode>(_frame));
          _stack.emplace_back(_Combine_INode{std::move(_result), _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_INode>(_frame));
          _result = inner::inode(_result, _f._s1, _f._result);
        }
      }
      return _result;
    }

    unsigned int inner_sum() const {
      const inner *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const inner *_self;
      };

      /// _After_INode: saves [_s0, d_a1], dispatches next recursive call.
      struct _After_INode {
        inner *_s0;
        unsigned int d_a1;
      };

      /// _Combine_INode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_INode {
        unsigned int _result;
        unsigned int d_a1;
      };

      using _Frame = std::variant<_Enter, _After_INode, _Combine_INode>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified inner_sum: _Enter -> _After_INode -> _Combine_INode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const inner *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename inner::ILeaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename inner::INode>(_sv.v());
            _stack.emplace_back(_After_INode{d_a0.get(), d_a1});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_INode>(_frame)) {
          auto _f = std::move(std::get<_After_INode>(_frame));
          _stack.emplace_back(_Combine_INode{_result, _f.d_a1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_INode>(_frame));
          _result = ((_result + _f.d_a1) + _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, inner &, T1 &, unsigned int &,
                                     inner &, T1 &>
    T1 inner_rec(const T1 f, F1 &&f0) const {
      const inner *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const inner *_self;
      };

      /// _After_INode: saves [_s0, d_a2, d_a1, d_a0], dispatches next recursive
      /// call.
      struct _After_INode {
        inner *_s0;
        inner d_a2;
        unsigned int d_a1;
        inner d_a0;
      };

      /// _Combine_INode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_INode {
        T1 _result;
        inner d_a2;
        unsigned int d_a1;
        inner d_a0;
      };

      using _Frame = std::variant<_Enter, _After_INode, _Combine_INode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified inner_rec: _Enter -> _After_INode -> _Combine_INode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const inner *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename inner::ILeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename inner::INode>(_sv.v());
            _stack.emplace_back(
                _After_INode{d_a0.get(), *(d_a2), d_a1, *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_INode>(_frame)) {
          auto _f = std::move(std::get<_After_INode>(_frame));
          _stack.emplace_back(_Combine_INode{_result, std::move(_f.d_a2),
                                             _f.d_a1, std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_INode>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f.d_a2, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, inner &, T1 &, unsigned int &,
                                     inner &, T1 &>
    T1 inner_rect(const T1 f, F1 &&f0) const {
      const inner *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const inner *_self;
      };

      /// _After_INode: saves [_s0, d_a2, d_a1, d_a0], dispatches next recursive
      /// call.
      struct _After_INode {
        inner *_s0;
        inner d_a2;
        unsigned int d_a1;
        inner d_a0;
      };

      /// _Combine_INode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_INode {
        T1 _result;
        inner d_a2;
        unsigned int d_a1;
        inner d_a0;
      };

      using _Frame = std::variant<_Enter, _After_INode, _Combine_INode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified inner_rect: _Enter -> _After_INode -> _Combine_INode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const inner *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename inner::ILeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename inner::INode>(_sv.v());
            _stack.emplace_back(
                _After_INode{d_a0.get(), *(d_a2), d_a1, *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_INode>(_frame)) {
          auto _f = std::move(std::get<_After_INode>(_frame));
          _stack.emplace_back(_Combine_INode{_result, std::move(_f.d_a2),
                                             _f.d_a1, std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_INode>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f.d_a2, _f._result);
        }
      }
      return _result;
    }
  };

  /// An outer tree type with an inner tree as a non-recursive field.
  struct outer {
    // TYPES
    struct OLeaf {};

    struct ONode {
      std::unique_ptr<outer> d_a0;
      inner d_a1;
      std::unique_ptr<outer> d_a2;
    };

    using variant_t = std::variant<OLeaf, ONode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    outer() {}

    explicit outer(OLeaf _v) : d_v_(_v) {}

    explicit outer(ONode _v) : d_v_(std::move(_v)) {}

    outer(const outer &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    outer(outer &&_other) : d_v_(std::move(_other.d_v_)) {}

    outer &operator=(const outer &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    outer &operator=(outer &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    outer clone() const {
      outer _out{};

      struct _CloneFrame {
        const outer *_src;
        outer *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const outer *_src = _frame._src;
        outer *_dst = _frame._dst;
        if (std::holds_alternative<OLeaf>(_src->v())) {
          _dst->d_v_ = OLeaf{};
        } else {
          const auto &_alt = std::get<ONode>(_src->v());
          _dst->d_v_ = ONode{_alt.d_a0 ? std::make_unique<outer>() : nullptr,
                             _alt.d_a1.clone(),
                             _alt.d_a2 ? std::make_unique<outer>() : nullptr};
          auto &_dst_alt = std::get<ONode>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static outer oleaf() { return outer(OLeaf{}); }

    static outer onode(outer a0, inner a1, outer a2) {
      return outer(ONode{std::make_unique<outer>(std::move(a0)), std::move(a1),
                         std::make_unique<outer>(std::move(a2))});
    }

    // MANIPULATORS
    ~outer() {
      std::vector<std::unique_ptr<outer>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](outer &_node) {
        if (std::holds_alternative<ONode>(_node.d_v_)) {
          auto &_alt = std::get<ONode>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
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

    /// TEST 6: Dup outer tree — use outer value twice.
    std::pair<outer, outer> dup_outer() const {
      return std::make_pair(*(this), *(this));
    }

    outer transform_outer() const {
      const outer *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const outer *_self;
      };

      /// _After_ONode: saves [_s0, d_a1], dispatches next recursive call.
      struct _After_ONode {
        outer *_s0;
        decltype(std::declval<inner &>().double_inner()) d_a1;
      };

      /// _Combine_ONode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_ONode {
        outer _result;
        decltype(std::declval<inner &>().double_inner()) d_a1;
      };

      using _Frame = std::variant<_Enter, _After_ONode, _Combine_ONode>;
      outer _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified transform_outer: _Enter -> _After_ONode -> _Combine_ONode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const outer *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename outer::OLeaf>(_sv.v())) {
            _result = outer::oleaf();
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename outer::ONode>(_sv.v());
            _stack.emplace_back(_After_ONode{d_a0.get(), d_a1.double_inner()});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_ONode>(_frame)) {
          auto _f = std::move(std::get<_After_ONode>(_frame));
          _stack.emplace_back(_Combine_ONode{std::move(_result), _f.d_a1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_ONode>(_frame));
          _result = outer::onode(_result, _f.d_a1, _f._result);
        }
      }
      return _result;
    }

    unsigned int outer_sum() const {
      const outer *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const outer *_self;
      };

      /// _After_ONode: saves [_s0, d_a1], dispatches next recursive call.
      struct _After_ONode {
        outer *_s0;
        decltype(std::declval<inner &>().inner_sum()) d_a1;
      };

      /// _Combine_ONode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_ONode {
        unsigned int _result;
        decltype(std::declval<inner &>().inner_sum()) d_a1;
      };

      using _Frame = std::variant<_Enter, _After_ONode, _Combine_ONode>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified outer_sum: _Enter -> _After_ONode -> _Combine_ONode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const outer *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename outer::OLeaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename outer::ONode>(_sv.v());
            _stack.emplace_back(_After_ONode{d_a0.get(), d_a1.inner_sum()});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_ONode>(_frame)) {
          auto _f = std::move(std::get<_After_ONode>(_frame));
          _stack.emplace_back(_Combine_ONode{_result, _f.d_a1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_ONode>(_frame));
          _result = ((_result + _f.d_a1) + _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, outer &, T1 &, inner &, outer &,
                                     T1 &>
    T1 outer_rec(const T1 f, F1 &&f0) const {
      const outer *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const outer *_self;
      };

      /// _After_ONode: saves [_s0, d_a2, d_a1, d_a0], dispatches next recursive
      /// call.
      struct _After_ONode {
        outer *_s0;
        outer d_a2;
        inner d_a1;
        outer d_a0;
      };

      /// _Combine_ONode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_ONode {
        T1 _result;
        outer d_a2;
        inner d_a1;
        outer d_a0;
      };

      using _Frame = std::variant<_Enter, _After_ONode, _Combine_ONode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified outer_rec: _Enter -> _After_ONode -> _Combine_ONode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const outer *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename outer::OLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename outer::ONode>(_sv.v());
            _stack.emplace_back(
                _After_ONode{d_a0.get(), *(d_a2), d_a1, *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_ONode>(_frame)) {
          auto _f = std::move(std::get<_After_ONode>(_frame));
          _stack.emplace_back(_Combine_ONode{_result, std::move(_f.d_a2),
                                             std::move(_f.d_a1),
                                             std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_ONode>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f.d_a2, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, outer &, T1 &, inner &, outer &,
                                     T1 &>
    T1 outer_rect(const T1 f, F1 &&f0) const {
      const outer *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const outer *_self;
      };

      /// _After_ONode: saves [_s0, d_a2, d_a1, d_a0], dispatches next recursive
      /// call.
      struct _After_ONode {
        outer *_s0;
        outer d_a2;
        inner d_a1;
        outer d_a0;
      };

      /// _Combine_ONode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_ONode {
        T1 _result;
        outer d_a2;
        inner d_a1;
        outer d_a0;
      };

      using _Frame = std::variant<_Enter, _After_ONode, _Combine_ONode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified outer_rect: _Enter -> _After_ONode -> _Combine_ONode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const outer *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename outer::OLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename outer::ONode>(_sv.v());
            _stack.emplace_back(
                _After_ONode{d_a0.get(), *(d_a2), d_a1, *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_ONode>(_frame)) {
          auto _f = std::move(std::get<_After_ONode>(_frame));
          _stack.emplace_back(_Combine_ONode{_result, std::move(_f.d_a2),
                                             std::move(_f.d_a1),
                                             std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_ONode>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f.d_a2, _f._result);
        }
      }
      return _result;
    }
  };

  /// An expression type with varying constructor arities.
  struct expr {
    // TYPES
    struct Lit {
      unsigned int d_a0;
    };

    struct Neg {
      std::unique_ptr<expr> d_a0;
    };

    struct Add {
      std::unique_ptr<expr> d_a0;
      std::unique_ptr<expr> d_a1;
    };

    struct Mul {
      std::unique_ptr<expr> d_a0;
      std::unique_ptr<expr> d_a1;
    };

    using variant_t = std::variant<Lit, Neg, Add, Mul>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Lit _v) : d_v_(std::move(_v)) {}

    explicit expr(Neg _v) : d_v_(std::move(_v)) {}

    explicit expr(Add _v) : d_v_(std::move(_v)) {}

    explicit expr(Mul _v) : d_v_(std::move(_v)) {}

    expr(const expr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    expr(expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    expr &operator=(const expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    expr &operator=(expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    expr clone() const {
      expr _out{};

      struct _CloneFrame {
        const expr *_src;
        expr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const expr *_src = _frame._src;
        expr *_dst = _frame._dst;
        if (std::holds_alternative<Lit>(_src->v())) {
          const auto &_alt = std::get<Lit>(_src->v());
          _dst->d_v_ = Lit{_alt.d_a0};
        } else if (std::holds_alternative<Neg>(_src->v())) {
          const auto &_alt = std::get<Neg>(_src->v());
          _dst->d_v_ = Neg{_alt.d_a0 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<Neg>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
        } else if (std::holds_alternative<Add>(_src->v())) {
          const auto &_alt = std::get<Add>(_src->v());
          _dst->d_v_ = Add{_alt.d_a0 ? std::make_unique<expr>() : nullptr,
                           _alt.d_a1 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<Add>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else {
          const auto &_alt = std::get<Mul>(_src->v());
          _dst->d_v_ = Mul{_alt.d_a0 ? std::make_unique<expr>() : nullptr,
                           _alt.d_a1 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<Mul>(_dst->d_v_);
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
    static expr lit(unsigned int a0) { return expr(Lit{std::move(a0)}); }

    static expr neg(expr a0) {
      return expr(Neg{std::make_unique<expr>(std::move(a0))});
    }

    static expr add(expr a0, expr a1) {
      return expr(Add{std::make_unique<expr>(std::move(a0)),
                      std::make_unique<expr>(std::move(a1))});
    }

    static expr mul(expr a0, expr a1) {
      return expr(Mul{std::make_unique<expr>(std::move(a0)),
                      std::make_unique<expr>(std::move(a1))});
    }

    // MANIPULATORS
    ~expr() {
      std::vector<std::unique_ptr<expr>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](expr &_node) {
        if (std::holds_alternative<Neg>(_node.d_v_)) {
          auto &_alt = std::get<Neg>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
        }
        if (std::holds_alternative<Add>(_node.d_v_)) {
          auto &_alt = std::get<Add>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<Mul>(_node.d_v_)) {
          auto &_alt = std::get<Mul>(_node.d_v_);
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

    /// TEST 8: Mixed operations — build outer from expr eval results,
    /// then transform. Cross-type interaction.
    inner expr_to_inner() const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _After_Add: saves [_s0, _s1], dispatches next recursive call.
      struct _After_Add {
        expr *_s0;
        decltype(0u) _s1;
      };

      /// _After_Mul: saves [_s0, _s1], dispatches next recursive call.
      struct _After_Mul {
        expr *_s0;
        decltype(1u) _s1;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        inner _result;
        decltype(0u) _s1;
      };

      /// _Combine_Mul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Mul {
        inner _result;
        decltype(1u) _s1;
      };

      using _Frame = std::variant<_Enter, _After_Add, _After_Mul, _Combine_Add,
                                  _Combine_Mul>;
      inner _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified expr_to_inner: _Enter -> _After_Add -> _After_Mul ->
      /// _Combine_Add -> _Combine_Mul.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Lit>(_sv.v());
            _result = inner::inode(inner::ileaf(), d_a0, inner::ileaf());
          } else if (std::holds_alternative<typename expr::Neg>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Neg>(_sv.v());
            _stack.emplace_back(_Enter{d_a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{d_a0.get(), 0u});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_After_Mul{d_a0.get(), 1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(_Combine_Add{std::move(_result), _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Mul>(_frame)) {
          auto _f = std::move(std::get<_After_Mul>(_frame));
          _stack.emplace_back(_Combine_Mul{std::move(_result), _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = inner::inode(_result, _f._s1, _f._result);
        } else {
          auto _f = std::move(std::get<_Combine_Mul>(_frame));
          _result = inner::inode(_result, _f._s1, _f._result);
        }
      }
      return _result;
    }

    /// TEST 7: Map over expr tree — rebuild with transformed values.
    expr double_expr() const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _After_Add: saves [_s0], dispatches next recursive call.
      struct _After_Add {
        expr *_s0;
      };

      /// _After_Mul: saves [_s0], dispatches next recursive call.
      struct _After_Mul {
        expr *_s0;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        expr _result;
      };

      /// _Combine_Mul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Mul {
        expr _result;
      };

      /// _Resume_Neg: resumes after recursive call with _result.
      struct _Resume_Neg {};

      using _Frame = std::variant<_Enter, _After_Add, _After_Mul, _Combine_Add,
                                  _Combine_Mul, _Resume_Neg>;
      expr _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified double_expr: _Enter -> _After_Add -> _After_Mul ->
      /// _Combine_Add -> _Combine_Mul -> _Resume_Neg.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Lit>(_sv.v());
            _result = expr::lit((d_a0 * 2u));
          } else if (std::holds_alternative<typename expr::Neg>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Neg>(_sv.v());
            _stack.emplace_back(_Resume_Neg{});
            _stack.emplace_back(_Enter{d_a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_After_Mul{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(_Combine_Add{std::move(_result)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Mul>(_frame)) {
          auto _f = std::move(std::get<_After_Mul>(_frame));
          _stack.emplace_back(_Combine_Mul{std::move(_result)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = expr::add(_result, _f._result);
        } else if (std::holds_alternative<_Combine_Mul>(_frame)) {
          auto _f = std::move(std::get<_Combine_Mul>(_frame));
          _result = expr::mul(_result, _f._result);
        } else {
          auto _f = std::move(std::get<_Resume_Neg>(_frame));
          _result = expr::neg(_result);
        }
      }
      return _result;
    }

    unsigned int eval_expr() const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _After_Add: saves [_s0], dispatches next recursive call.
      struct _After_Add {
        expr *_s0;
      };

      /// _After_Mul: saves [_s0], dispatches next recursive call.
      struct _After_Mul {
        expr *_s0;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        unsigned int _result;
      };

      /// _Combine_Mul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Mul {
        unsigned int _result;
      };

      using _Frame = std::variant<_Enter, _After_Add, _After_Mul, _Combine_Add,
                                  _Combine_Mul>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified eval_expr: _Enter -> _After_Add -> _After_Mul ->
      /// _Combine_Add -> _Combine_Mul.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Lit>(_sv.v());
            _result = d_a0;
          } else if (std::holds_alternative<typename expr::Neg>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Neg>(_sv.v());
            _stack.emplace_back(_Enter{d_a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_After_Mul{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(_Combine_Add{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Mul>(_frame)) {
          auto _f = std::move(std::get<_After_Mul>(_frame));
          _stack.emplace_back(_Combine_Mul{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = (_result + _f._result);
        } else {
          auto _f = std::move(std::get<_Combine_Mul>(_frame));
          _result = (_result * _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F3 &, expr &, T1 &, expr &, T1 &>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _After_Add: saves [_s0, d_a1, d_a0], dispatches next recursive call.
      struct _After_Add {
        expr *_s0;
        expr d_a1;
        expr d_a0;
      };

      /// _After_Mul: saves [_s0, d_a1, d_a0], dispatches next recursive call.
      struct _After_Mul {
        expr *_s0;
        expr d_a1;
        expr d_a0;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        T1 _result;
        expr d_a1;
        expr d_a0;
      };

      /// _Combine_Mul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Mul {
        T1 _result;
        expr d_a1;
        expr d_a0;
      };

      /// _Resume_Neg: saves [f0, d_a0], resumes after recursive call with
      /// _result.
      struct _Resume_Neg {
        F1 f0;
        expr d_a0;
      };

      using _Frame = std::variant<_Enter, _After_Add, _After_Mul, _Combine_Add,
                                  _Combine_Mul, _Resume_Neg>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified expr_rec: _Enter -> _After_Add -> _After_Mul -> _Combine_Add
      /// -> _Combine_Mul -> _Resume_Neg.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Lit>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename expr::Neg>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Neg>(_sv.v());
            _stack.emplace_back(_Resume_Neg{f0, *(d_a0)});
            _stack.emplace_back(_Enter{d_a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_After_Mul{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(
              _Combine_Add{_result, std::move(_f.d_a1), std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Mul>(_frame)) {
          auto _f = std::move(std::get<_After_Mul>(_frame));
          _stack.emplace_back(
              _Combine_Mul{_result, std::move(_f.d_a1), std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = f1(_f.d_a0, _result, _f.d_a1, _f._result);
        } else if (std::holds_alternative<_Combine_Mul>(_frame)) {
          auto _f = std::move(std::get<_Combine_Mul>(_frame));
          _result = f2(_f.d_a0, _result, _f.d_a1, _f._result);
        } else {
          auto _f = std::move(std::get<_Resume_Neg>(_frame));
          _result = _f.f0(_f.d_a0, _result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F3 &, expr &, T1 &, expr &, T1 &>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _After_Add: saves [_s0, d_a1, d_a0], dispatches next recursive call.
      struct _After_Add {
        expr *_s0;
        expr d_a1;
        expr d_a0;
      };

      /// _After_Mul: saves [_s0, d_a1, d_a0], dispatches next recursive call.
      struct _After_Mul {
        expr *_s0;
        expr d_a1;
        expr d_a0;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        T1 _result;
        expr d_a1;
        expr d_a0;
      };

      /// _Combine_Mul: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Mul {
        T1 _result;
        expr d_a1;
        expr d_a0;
      };

      /// _Resume_Neg: saves [f0, d_a0], resumes after recursive call with
      /// _result.
      struct _Resume_Neg {
        F1 f0;
        expr d_a0;
      };

      using _Frame = std::variant<_Enter, _After_Add, _After_Mul, _Combine_Add,
                                  _Combine_Mul, _Resume_Neg>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified expr_rect: _Enter -> _After_Add -> _After_Mul ->
      /// _Combine_Add -> _Combine_Mul -> _Resume_Neg.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Lit>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename expr::Neg>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Neg>(_sv.v());
            _stack.emplace_back(_Resume_Neg{f0, *(d_a0)});
            _stack.emplace_back(_Enter{d_a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_After_Mul{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(
              _Combine_Add{_result, std::move(_f.d_a1), std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_Mul>(_frame)) {
          auto _f = std::move(std::get<_After_Mul>(_frame));
          _stack.emplace_back(
              _Combine_Mul{_result, std::move(_f.d_a1), std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Combine_Add>(_frame)) {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = f1(_f.d_a0, _result, _f.d_a1, _f._result);
        } else if (std::holds_alternative<_Combine_Mul>(_frame)) {
          auto _f = std::move(std::get<_Combine_Mul>(_frame));
          _result = f2(_f.d_a0, _result, _f.d_a1, _f._result);
        } else {
          auto _f = std::move(std::get<_Resume_Neg>(_frame));
          _result = _f.f0(_f.d_a0, _result);
        }
      }
      return _result;
    }
  };

  /// A three-child tree.
  struct tree3 {
    // TYPES
    struct T3Leaf {};

    struct T3Node {
      std::unique_ptr<tree3> d_a0;
      std::unique_ptr<tree3> d_a1;
      std::unique_ptr<tree3> d_a2;
      unsigned int d_a3;
    };

    using variant_t = std::variant<T3Leaf, T3Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree3() {}

    explicit tree3(T3Leaf _v) : d_v_(_v) {}

    explicit tree3(T3Node _v) : d_v_(std::move(_v)) {}

    tree3(const tree3 &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree3(tree3 &&_other) : d_v_(std::move(_other.d_v_)) {}

    tree3 &operator=(const tree3 &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tree3 &operator=(tree3 &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    tree3 clone() const {
      tree3 _out{};

      struct _CloneFrame {
        const tree3 *_src;
        tree3 *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree3 *_src = _frame._src;
        tree3 *_dst = _frame._dst;
        if (std::holds_alternative<T3Leaf>(_src->v())) {
          _dst->d_v_ = T3Leaf{};
        } else {
          const auto &_alt = std::get<T3Node>(_src->v());
          _dst->d_v_ = T3Node{_alt.d_a0 ? std::make_unique<tree3>() : nullptr,
                              _alt.d_a1 ? std::make_unique<tree3>() : nullptr,
                              _alt.d_a2 ? std::make_unique<tree3>() : nullptr,
                              _alt.d_a3};
          auto &_dst_alt = std::get<T3Node>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
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
    static tree3 t3leaf() { return tree3(T3Leaf{}); }

    static tree3 t3node(tree3 a0, tree3 a1, tree3 a2, unsigned int a3) {
      return tree3(T3Node{std::make_unique<tree3>(std::move(a0)),
                          std::make_unique<tree3>(std::move(a1)),
                          std::make_unique<tree3>(std::move(a2)),
                          std::move(a3)});
    }

    // MANIPULATORS
    ~tree3() {
      std::vector<std::unique_ptr<tree3>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree3 &_node) {
        if (std::holds_alternative<T3Node>(_node.d_v_)) {
          auto &_alt = std::get<T3Node>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
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

    unsigned int tree3_sum() const {
      const tree3 *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree3 *_self;
      };

      /// _After_T3Node: saves [_s0, _s1, d_a3], dispatches next recursive call.
      struct _After_T3Node {
        const tree3 *_s0;
        const tree3 *_s1;
        unsigned int d_a3;
      };

      /// _After_T3Node_1: saves [_result, _s1, d_a3], dispatches next recursive
      /// call.
      struct _After_T3Node_1 {
        unsigned int _result;
        const tree3 *_s1;
        unsigned int d_a3;
      };

      /// _Combine_T3Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_T3Node {
        unsigned int _result_0;
        unsigned int _result_1;
        unsigned int d_a3;
      };

      using _Frame =
          std::variant<_Enter, _After_T3Node, _After_T3Node_1, _Combine_T3Node>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree3_sum: _Enter -> _After_T3Node -> _After_T3Node_1 ->
      /// _Combine_T3Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree3 *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree3::T3Leaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename tree3::T3Node>(_sv.v());
            _stack.emplace_back(_After_T3Node{d_a1.get(), d_a0.get(), d_a3});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_T3Node>(_frame)) {
          auto _f = std::move(std::get<_After_T3Node>(_frame));
          _stack.emplace_back(_After_T3Node_1{_result, _f._s1, _f.d_a3});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_T3Node_1>(_frame)) {
          auto _f = std::move(std::get<_After_T3Node_1>(_frame));
          _stack.emplace_back(_Combine_T3Node{_f._result, _result, _f.d_a3});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Combine_T3Node>(_frame));
          _result = (((_result + _f._result_1) + _f._result_0) + _f.d_a3);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree3 &, T1 &, tree3 &, T1 &,
                                     tree3 &, T1 &, unsigned int &>
    T1 tree3_rec(const T1 f, F1 &&f0) const {
      const tree3 *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree3 *_self;
      };

      /// _After_T3Node: saves [_s0, _s1, d_a3, d_a2, d_a1, d_a0], dispatches
      /// next recursive call.
      struct _After_T3Node {
        const tree3 *_s0;
        const tree3 *_s1;
        unsigned int d_a3;
        tree3 d_a2;
        tree3 d_a1;
        tree3 d_a0;
      };

      /// _After_T3Node_1: saves [_result, _s1, d_a3, d_a2, d_a1, d_a0],
      /// dispatches next recursive call.
      struct _After_T3Node_1 {
        T1 _result;
        const tree3 *_s1;
        unsigned int d_a3;
        tree3 d_a2;
        tree3 d_a1;
        tree3 d_a0;
      };

      /// _Combine_T3Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_T3Node {
        T1 _result_0;
        T1 _result_1;
        unsigned int d_a3;
        tree3 d_a2;
        tree3 d_a1;
        tree3 d_a0;
      };

      using _Frame =
          std::variant<_Enter, _After_T3Node, _After_T3Node_1, _Combine_T3Node>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree3_rec: _Enter -> _After_T3Node -> _After_T3Node_1 ->
      /// _Combine_T3Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree3 *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree3::T3Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename tree3::T3Node>(_sv.v());
            _stack.emplace_back(_After_T3Node{d_a1.get(), d_a0.get(), d_a3,
                                              *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_T3Node>(_frame)) {
          auto _f = std::move(std::get<_After_T3Node>(_frame));
          _stack.emplace_back(
              _After_T3Node_1{_result, _f._s1, _f.d_a3, std::move(_f.d_a2),
                              std::move(_f.d_a1), std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_T3Node_1>(_frame)) {
          auto _f = std::move(std::get<_After_T3Node_1>(_frame));
          _stack.emplace_back(
              _Combine_T3Node{_f._result, _result, _f.d_a3, std::move(_f.d_a2),
                              std::move(_f.d_a1), std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Combine_T3Node>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f._result_1, _f.d_a2,
                       _f._result_0, _f.d_a3);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree3 &, T1 &, tree3 &, T1 &,
                                     tree3 &, T1 &, unsigned int &>
    T1 tree3_rect(const T1 f, F1 &&f0) const {
      const tree3 *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree3 *_self;
      };

      /// _After_T3Node: saves [_s0, _s1, d_a3, d_a2, d_a1, d_a0], dispatches
      /// next recursive call.
      struct _After_T3Node {
        const tree3 *_s0;
        const tree3 *_s1;
        unsigned int d_a3;
        tree3 d_a2;
        tree3 d_a1;
        tree3 d_a0;
      };

      /// _After_T3Node_1: saves [_result, _s1, d_a3, d_a2, d_a1, d_a0],
      /// dispatches next recursive call.
      struct _After_T3Node_1 {
        T1 _result;
        const tree3 *_s1;
        unsigned int d_a3;
        tree3 d_a2;
        tree3 d_a1;
        tree3 d_a0;
      };

      /// _Combine_T3Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_T3Node {
        T1 _result_0;
        T1 _result_1;
        unsigned int d_a3;
        tree3 d_a2;
        tree3 d_a1;
        tree3 d_a0;
      };

      using _Frame =
          std::variant<_Enter, _After_T3Node, _After_T3Node_1, _Combine_T3Node>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree3_rect: _Enter -> _After_T3Node -> _After_T3Node_1 ->
      /// _Combine_T3Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree3 *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree3::T3Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename tree3::T3Node>(_sv.v());
            _stack.emplace_back(_After_T3Node{d_a1.get(), d_a0.get(), d_a3,
                                              *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_T3Node>(_frame)) {
          auto _f = std::move(std::get<_After_T3Node>(_frame));
          _stack.emplace_back(
              _After_T3Node_1{_result, _f._s1, _f.d_a3, std::move(_f.d_a2),
                              std::move(_f.d_a1), std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_T3Node_1>(_frame)) {
          auto _f = std::move(std::get<_After_T3Node_1>(_frame));
          _stack.emplace_back(
              _Combine_T3Node{_f._result, _result, _f.d_a3, std::move(_f.d_a2),
                              std::move(_f.d_a1), std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Combine_T3Node>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f._result_1, _f.d_a2,
                       _f._result_0, _f.d_a3);
        }
      }
      return _result;
    }
  };

  /// TEST 1: Build and sum an outer tree with inner tree values.
  /// Tests nested value-type clone/destructor interaction.
  static inline const unsigned int test_outer_basic = []() {
    outer o = outer::onode(
        outer::onode(outer::oleaf(),
                     inner::inode(inner::ileaf(), 10u, inner::ileaf()),
                     outer::oleaf()),
        inner::inode(inner::inode(inner::ileaf(), 1u, inner::ileaf()), 2u,
                     inner::inode(inner::ileaf(), 3u, inner::ileaf())),
        outer::onode(outer::oleaf(),
                     inner::inode(inner::ileaf(), 20u, inner::ileaf()),
                     outer::oleaf()));
    return std::move(o).outer_sum();
  }();
  /// TEST 2: Dup pattern — use inner tree twice in outer construction.
  static outer dup_inner(inner i);
  static inline const unsigned int test_dup_inner = []() {
    inner i =
        inner::inode(inner::inode(inner::ileaf(), 5u, inner::ileaf()), 10u,
                     inner::inode(inner::ileaf(), 15u, inner::ileaf()));
    return dup_inner(std::move(i)).outer_sum();
  }();
  static inline const unsigned int test_transform = []() {
    outer o = outer::onode(
        outer::oleaf(), inner::inode(inner::ileaf(), 5u, inner::ileaf()),
        outer::onode(outer::oleaf(),
                     inner::inode(inner::ileaf(), 10u, inner::ileaf()),
                     outer::oleaf()));
    return std::move(o).transform_outer().outer_sum();
  }();
  /// TEST 4: Build and evaluate a complex expression tree.
  static inline const unsigned int test_expr = []() {
    expr e = expr::add(
        expr::mul(expr::add(expr::lit(2u), expr::lit(3u)), expr::lit(4u)),
        expr::neg(expr::add(expr::lit(10u), expr::lit(5u))));
    return std::move(e).eval_expr();
  }();
  /// TEST 5: Deep 3-child tree to stress clone/destructor.
  static tree3 build_tree3(const unsigned int n);
  static inline const unsigned int test_tree3 = build_tree3(4u).tree3_sum();
  static inline const unsigned int test_dup_outer = []() {
    outer o = outer::onode(outer::oleaf(),
                           inner::inode(inner::ileaf(), 42u, inner::ileaf()),
                           outer::oleaf());
    std::pair<outer, outer> p = std::move(o).dup_outer();
    return (p.first.outer_sum() + p.second.outer_sum());
  }();
  static inline const unsigned int test_double_expr =
      expr::add(expr::lit(5u), expr::mul(expr::lit(3u), expr::lit(7u)))
          .double_expr()
          .eval_expr();
  static inline const unsigned int test_cross_type = []() {
    expr e = expr::add(expr::lit(5u), expr::mul(expr::lit(3u), expr::lit(7u)));
    inner i = std::move(e).expr_to_inner();
    outer o = outer::onode(outer::oleaf(), i, outer::oleaf());
    return (std::move(o).outer_sum() + std::move(i).inner_sum());
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE29
