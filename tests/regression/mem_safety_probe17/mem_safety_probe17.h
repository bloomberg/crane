#ifndef INCLUDED_MEM_SAFETY_PROBE17
#define INCLUDED_MEM_SAFETY_PROBE17

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe17 {
  /// Probe 17: Wide tree (4-ary) and complex ownership patterns.
  ///
  /// Attack vectors:
  /// 1. 4-ary tree with 4 unique_ptr children -- more complex frame structs
  /// 2. Functions that use ALL children in computations AND recursive calls
  /// 3. Owned match where one child is used in a closure AND others
  /// in recursive calls (testing pre-extraction with many children)
  /// 4. Mutual-like patterns where different functions process the
  /// same tree differently
  struct qtree {
    // TYPES
    struct QLeaf {};

    struct QNode {
      std::unique_ptr<qtree> a0;
      std::unique_ptr<qtree> a1;
      unsigned int a2;
      std::unique_ptr<qtree> a3;
      std::unique_ptr<qtree> a4;
    };

    using variant_t = std::variant<QLeaf, QNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    qtree() {}

    explicit qtree(QLeaf _v) : v_(_v) {}

    explicit qtree(QNode _v) : v_(std::move(_v)) {}

    qtree(const qtree &_other) : v_(std::move(_other.clone().v_)) {}

    qtree(qtree &&_other) noexcept : v_(std::move(_other.v_)) {}

    qtree &operator=(const qtree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    qtree &operator=(qtree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    qtree clone() const {
      qtree _out{};

      struct _CloneFrame {
        const qtree *_src;
        qtree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const qtree *_src = _frame._src;
        qtree *_dst = _frame._dst;
        if (std::holds_alternative<QLeaf>(_src->v())) {
          _dst->v_ = QLeaf{};
        } else {
          const auto &_alt = std::get<QNode>(_src->v());
          _dst->v_ =
              QNode{_alt.a0 ? std::make_unique<qtree>() : nullptr,
                    _alt.a1 ? std::make_unique<qtree>() : nullptr, _alt.a2,
                    _alt.a3 ? std::make_unique<qtree>() : nullptr,
                    _alt.a4 ? std::make_unique<qtree>() : nullptr};
          auto &_dst_alt = std::get<QNode>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
          if (_alt.a3) {
            _stack.push_back({_alt.a3.get(), _dst_alt.a3.get()});
          }
          if (_alt.a4) {
            _stack.push_back({_alt.a4.get(), _dst_alt.a4.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static qtree qleaf() { return qtree(QLeaf{}); }

    static qtree qnode(qtree a0, qtree a1, unsigned int a2, qtree a3,
                       qtree a4) {
      return qtree(QNode{std::make_unique<qtree>(std::move(a0)),
                         std::make_unique<qtree>(std::move(a1)), a2,
                         std::make_unique<qtree>(std::move(a3)),
                         std::make_unique<qtree>(std::move(a4))});
    }

    // MANIPULATORS
    ~qtree() {
      std::vector<std::unique_ptr<qtree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](qtree &_node) {
        if (std::holds_alternative<QNode>(_node.v_)) {
          auto &_alt = std::get<QNode>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
          if (_alt.a3) {
            _stack.push_back(std::move(_alt.a3));
          }
          if (_alt.a4) {
            _stack.push_back(std::move(_alt.a4));
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

    /// TEST 6: Compute a value using ALL children non-recursively,
    /// THEN use all children recursively. Tests frame saving with
    /// many unique_ptr fields.
    unsigned int weighted_sum() const {
      const qtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const qtree *_self;
      };

      /// _After_QNode: saves [_s0, _s1, _s2, local_weight], dispatches next
      /// recursive call.
      struct _After_QNode {
        const qtree *_s0;
        const qtree *_s1;
        const qtree *_s2;
        unsigned int local_weight;
      };

      /// _After_QNode_1: saves [_result, _s1, _s2, local_weight], dispatches
      /// next recursive call.
      struct _After_QNode_1 {
        unsigned int _result;
        const qtree *_s1;
        const qtree *_s2;
        unsigned int local_weight;
      };

      /// _After_QNode_2: saves [_result_0, _result_1, _s2, local_weight],
      /// dispatches next recursive call.
      struct _After_QNode_2 {
        unsigned int _result_0;
        unsigned int _result_1;
        const qtree *_s2;
        unsigned int local_weight;
      };

      /// _Combine_QNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_QNode {
        unsigned int _result_0;
        unsigned int _result_1;
        unsigned int _result_2;
        unsigned int local_weight;
      };

      using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                                  _After_QNode_2, _Combine_QNode>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified weighted_sum: _Enter -> _After_QNode -> _After_QNode_1 ->
      /// _After_QNode_2 -> _Combine_QNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            unsigned int local_weight =
                (((((*a0).qtree_sum() + (2u * (*a1).qtree_sum())) + (3u * a2)) +
                  (4u * (*a3).qtree_sum())) +
                 (5u * (*a4).qtree_sum()));
            _stack.emplace_back(
                _After_QNode{a3.get(), a1.get(), a0.get(), local_weight});
            _stack.emplace_back(_Enter{a4.get()});
          }
        } else if (std::holds_alternative<_After_QNode>(_frame)) {
          auto _f = std::move(std::get<_After_QNode>(_frame));
          _stack.emplace_back(
              _After_QNode_1{_result, _f._s1, _f._s2, _f.local_weight});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_1>(_frame));
          _stack.emplace_back(
              _After_QNode_2{_f._result, _result, _f._s2, _f.local_weight});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_2>(_frame));
          _stack.emplace_back(_Combine_QNode{_f._result_0, _f._result_1,
                                             _result, _f.local_weight});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Combine_QNode>(_frame));
          _result =
              ((((_f.local_weight + _result) + _f._result_2) + _f._result_1) +
               _f._result_0);
        }
      }
      return _result;
    }

    /// TEST 5: Zip two 4-ary trees.
    qtree qtree_zip(qtree t2) const {
      const qtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const qtree *_self;
        qtree t2;
      };

      /// _After_QNode: saves [_s0, a30, _s2, a10, _s4, a00, _s6], dispatches
      /// next recursive call.
      struct _After_QNode {
        const qtree *_s0;
        qtree a30;
        const qtree *_s2;
        qtree a10;
        const qtree *_s4;
        qtree a00;
        unsigned int _s6;
      };

      /// _After_QNode_1: saves [_result, _s1, a10, _s3, a00, _s5], dispatches
      /// next recursive call.
      struct _After_QNode_1 {
        qtree _result;
        const qtree *_s1;
        qtree a10;
        const qtree *_s3;
        qtree a00;
        unsigned int _s5;
      };

      /// _After_QNode_2: saves [_result_0, _result_1, _s2, a00, _s4],
      /// dispatches next recursive call.
      struct _After_QNode_2 {
        qtree _result_0;
        qtree _result_1;
        const qtree *_s2;
        qtree a00;
        unsigned int _s4;
      };

      /// _Combine_QNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_QNode {
        qtree _result_0;
        qtree _result_1;
        qtree _result_2;
        unsigned int _s3;
      };

      using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                                  _After_QNode_2, _Combine_QNode>;
      qtree _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self, t2});
      /// Loopified qtree_zip: _Enter -> _After_QNode -> _After_QNode_1 ->
      /// _After_QNode_2 -> _Combine_QNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const qtree *_self = _f._self;
          qtree t2 = std::move(_f.t2);
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = std::move(t2);
          } else {
            const auto &[a0, a2, a3, a4, a5] =
                std::get<typename qtree::QNode>(_sv.v());
            if (std::holds_alternative<typename qtree::QLeaf>(t2.v_mut())) {
              _result = *_self;
            } else {
              auto &[a00, a10, a20, a30, a40] =
                  std::get<typename qtree::QNode>(t2.v_mut());
              _stack.emplace_back(
                  _After_QNode{a4.get(), *a30, a2.get(), *a10, a0.get(), *a00,
                               (std::move(a3) + std::move(a20))});
              _stack.emplace_back(_Enter{a5.get(), std::move(*a40)});
            }
          }
        } else if (std::holds_alternative<_After_QNode>(_frame)) {
          auto _f = std::move(std::get<_After_QNode>(_frame));
          _stack.emplace_back(_After_QNode_1{std::move(_result), _f._s2,
                                             std::move(_f.a10), _f._s4,
                                             std::move(_f.a00), _f._s6});
          _stack.emplace_back(_Enter{_f._s0, std::move(_f.a30)});
        } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_1>(_frame));
          _stack.emplace_back(_After_QNode_2{std::move(_f._result),
                                             std::move(_result), _f._s3,
                                             std::move(_f.a00), _f._s5});
          _stack.emplace_back(_Enter{_f._s1, std::move(_f.a10)});
        } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_2>(_frame));
          _stack.emplace_back(_Combine_QNode{std::move(_f._result_0),
                                             std::move(_f._result_1),
                                             std::move(_result), _f._s4});
          _stack.emplace_back(_Enter{_f._s2, std::move(_f.a00)});
        } else {
          auto _f = std::move(std::get<_Combine_QNode>(_frame));
          _result = qtree::qnode(_result, _f._result_2, _f._s3, _f._result_1,
                                 _f._result_0);
        }
      }
      return _result;
    }

    /// TEST 3: Mirror a 4-ary tree (reverse children order).
    qtree qtree_mirror() const {
      const qtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const qtree *_self;
      };

      /// _After_QNode: saves [_s0, _s1, _s2, a2], dispatches next recursive
      /// call.
      struct _After_QNode {
        const qtree *_s0;
        const qtree *_s1;
        const qtree *_s2;
        unsigned int a2;
      };

      /// _After_QNode_1: saves [_result, _s1, _s2, a2], dispatches next
      /// recursive call.
      struct _After_QNode_1 {
        qtree _result;
        const qtree *_s1;
        const qtree *_s2;
        unsigned int a2;
      };

      /// _After_QNode_2: saves [_result_0, _result_1, _s2, a2], dispatches next
      /// recursive call.
      struct _After_QNode_2 {
        qtree _result_0;
        qtree _result_1;
        const qtree *_s2;
        unsigned int a2;
      };

      /// _Combine_QNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_QNode {
        qtree _result_0;
        qtree _result_1;
        qtree _result_2;
        unsigned int a2;
      };

      using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                                  _After_QNode_2, _Combine_QNode>;
      qtree _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified qtree_mirror: _Enter -> _After_QNode -> _After_QNode_1 ->
      /// _After_QNode_2 -> _Combine_QNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = qtree::qleaf();
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(_After_QNode{a1.get(), a3.get(), a4.get(), a2});
            _stack.emplace_back(_Enter{a0.get()});
          }
        } else if (std::holds_alternative<_After_QNode>(_frame)) {
          auto _f = std::move(std::get<_After_QNode>(_frame));
          _stack.emplace_back(
              _After_QNode_1{std::move(_result), _f._s1, _f._s2, _f.a2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_1>(_frame));
          _stack.emplace_back(_After_QNode_2{
              std::move(_f._result), std::move(_result), _f._s2, _f.a2});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_2>(_frame));
          _stack.emplace_back(_Combine_QNode{std::move(_f._result_0),
                                             std::move(_f._result_1),
                                             std::move(_result), _f.a2});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Combine_QNode>(_frame));
          _result = qtree::qnode(_result, _f._result_2, _f.a2, _f._result_1,
                                 _f._result_0);
        }
      }
      return _result;
    }

    unsigned int qtree_size() const {
      const qtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const qtree *_self;
      };

      /// _After_QNode: saves [_s0, _s1, _s2, _s3], dispatches next recursive
      /// call.
      struct _After_QNode {
        const qtree *_s0;
        const qtree *_s1;
        const qtree *_s2;
        decltype(1u) _s3;
      };

      /// _After_QNode_1: saves [_result, _s1, _s2, _s3], dispatches next
      /// recursive call.
      struct _After_QNode_1 {
        unsigned int _result;
        const qtree *_s1;
        const qtree *_s2;
        decltype(1u) _s3;
      };

      /// _After_QNode_2: saves [_result_0, _result_1, _s2, _s3], dispatches
      /// next recursive call.
      struct _After_QNode_2 {
        unsigned int _result_0;
        unsigned int _result_1;
        const qtree *_s2;
        decltype(1u) _s3;
      };

      /// _Combine_QNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_QNode {
        unsigned int _result_0;
        unsigned int _result_1;
        unsigned int _result_2;
        decltype(1u) _s3;
      };

      using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                                  _After_QNode_2, _Combine_QNode>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified qtree_size: _Enter -> _After_QNode -> _After_QNode_1 ->
      /// _After_QNode_2 -> _Combine_QNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(_After_QNode{a3.get(), a1.get(), a0.get(), 1u});
            _stack.emplace_back(_Enter{a4.get()});
          }
        } else if (std::holds_alternative<_After_QNode>(_frame)) {
          auto _f = std::move(std::get<_After_QNode>(_frame));
          _stack.emplace_back(_After_QNode_1{_result, _f._s1, _f._s2, _f._s3});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_1>(_frame));
          _stack.emplace_back(
              _After_QNode_2{_f._result, _result, _f._s2, _f._s3});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_2>(_frame));
          _stack.emplace_back(
              _Combine_QNode{_f._result_0, _f._result_1, _result, _f._s3});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Combine_QNode>(_frame));
          _result = ((((_f._s3 + _result) + _f._result_2) + _f._result_1) +
                     _f._result_0);
        }
      }
      return _result;
    }

    unsigned int qtree_depth() const {
      const qtree *_self = this;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
        return 0u;
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename qtree::QNode>(_sv.v());
        unsigned int da = (*a0).qtree_depth();
        unsigned int db = (*a1).qtree_depth();
        unsigned int dc = (*a3).qtree_depth();
        unsigned int dd = (*a4).qtree_depth();
        unsigned int m1;
        if (da <= db) {
          m1 = db;
        } else {
          m1 = da;
        }
        unsigned int m2;
        if (dc <= dd) {
          m2 = dd;
        } else {
          m2 = dc;
        }
        return (1u + (m1 <= m2 ? m2 : m1));
      }
    }

    unsigned int qtree_sum() const {
      const qtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const qtree *_self;
      };

      /// _After_QNode: saves [_s0, _s1, _s2, a2], dispatches next recursive
      /// call.
      struct _After_QNode {
        const qtree *_s0;
        const qtree *_s1;
        const qtree *_s2;
        unsigned int a2;
      };

      /// _After_QNode_1: saves [_result, _s1, _s2, a2], dispatches next
      /// recursive call.
      struct _After_QNode_1 {
        unsigned int _result;
        const qtree *_s1;
        const qtree *_s2;
        unsigned int a2;
      };

      /// _After_QNode_2: saves [_result_0, _result_1, _s2, a2], dispatches next
      /// recursive call.
      struct _After_QNode_2 {
        unsigned int _result_0;
        unsigned int _result_1;
        const qtree *_s2;
        unsigned int a2;
      };

      /// _Combine_QNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_QNode {
        unsigned int _result_0;
        unsigned int _result_1;
        unsigned int _result_2;
        unsigned int a2;
      };

      using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                                  _After_QNode_2, _Combine_QNode>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified qtree_sum: _Enter -> _After_QNode -> _After_QNode_1 ->
      /// _After_QNode_2 -> _Combine_QNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(_After_QNode{a3.get(), a1.get(), a0.get(), a2});
            _stack.emplace_back(_Enter{a4.get()});
          }
        } else if (std::holds_alternative<_After_QNode>(_frame)) {
          auto _f = std::move(std::get<_After_QNode>(_frame));
          _stack.emplace_back(_After_QNode_1{_result, _f._s1, _f._s2, _f.a2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_1>(_frame));
          _stack.emplace_back(
              _After_QNode_2{_f._result, _result, _f._s2, _f.a2});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_2>(_frame));
          _stack.emplace_back(
              _Combine_QNode{_f._result_0, _f._result_1, _result, _f.a2});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Combine_QNode>(_frame));
          _result = ((((_result + _f._result_2) + _f.a2) + _f._result_1) +
                     _f._result_0);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, qtree &, T1 &, qtree &, T1 &,
                                     unsigned int &, qtree &, T1 &, qtree &,
                                     T1 &>
    T1 qtree_rec(T1 f, F1 &&f0) const {
      const qtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const qtree *_self;
      };

      /// _After_QNode: saves [_s0, _s1, _s2, a4, a3, a2, a1, a0], dispatches
      /// next recursive call.
      struct _After_QNode {
        const qtree *_s0;
        const qtree *_s1;
        const qtree *_s2;
        qtree a4;
        qtree a3;
        unsigned int a2;
        qtree a1;
        qtree a0;
      };

      /// _After_QNode_1: saves [_result, _s1, _s2, a4, a3, a2, a1, a0],
      /// dispatches next recursive call.
      struct _After_QNode_1 {
        T1 _result;
        const qtree *_s1;
        const qtree *_s2;
        qtree a4;
        qtree a3;
        unsigned int a2;
        qtree a1;
        qtree a0;
      };

      /// _After_QNode_2: saves [_result_0, _result_1, _s2, a4, a3, a2, a1, a0],
      /// dispatches next recursive call.
      struct _After_QNode_2 {
        T1 _result_0;
        T1 _result_1;
        const qtree *_s2;
        qtree a4;
        qtree a3;
        unsigned int a2;
        qtree a1;
        qtree a0;
      };

      /// _Combine_QNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_QNode {
        T1 _result_0;
        T1 _result_1;
        T1 _result_2;
        qtree a4;
        qtree a3;
        unsigned int a2;
        qtree a1;
        qtree a0;
      };

      using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                                  _After_QNode_2, _Combine_QNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified qtree_rec: _Enter -> _After_QNode -> _After_QNode_1 ->
      /// _After_QNode_2 -> _Combine_QNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(_After_QNode{a3.get(), a1.get(), a0.get(), *a4,
                                             *a3, a2, *a1, *a0});
            _stack.emplace_back(_Enter{a4.get()});
          }
        } else if (std::holds_alternative<_After_QNode>(_frame)) {
          auto _f = std::move(std::get<_After_QNode>(_frame));
          _stack.emplace_back(_After_QNode_1{
              _result, _f._s1, _f._s2, std::move(_f.a4), std::move(_f.a3),
              _f.a2, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_1>(_frame));
          _stack.emplace_back(_After_QNode_2{
              _f._result, _result, _f._s2, std::move(_f.a4), std::move(_f.a3),
              _f.a2, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_2>(_frame));
          _stack.emplace_back(_Combine_QNode{
              _f._result_0, _f._result_1, _result, std::move(_f.a4),
              std::move(_f.a3), _f.a2, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Combine_QNode>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result_2, _f.a2, _f.a3,
                       _f._result_1, _f.a4, _f._result_0);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, qtree &, T1 &, qtree &, T1 &,
                                     unsigned int &, qtree &, T1 &, qtree &,
                                     T1 &>
    T1 qtree_rect(T1 f, F1 &&f0) const {
      const qtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const qtree *_self;
      };

      /// _After_QNode: saves [_s0, _s1, _s2, a4, a3, a2, a1, a0], dispatches
      /// next recursive call.
      struct _After_QNode {
        const qtree *_s0;
        const qtree *_s1;
        const qtree *_s2;
        qtree a4;
        qtree a3;
        unsigned int a2;
        qtree a1;
        qtree a0;
      };

      /// _After_QNode_1: saves [_result, _s1, _s2, a4, a3, a2, a1, a0],
      /// dispatches next recursive call.
      struct _After_QNode_1 {
        T1 _result;
        const qtree *_s1;
        const qtree *_s2;
        qtree a4;
        qtree a3;
        unsigned int a2;
        qtree a1;
        qtree a0;
      };

      /// _After_QNode_2: saves [_result_0, _result_1, _s2, a4, a3, a2, a1, a0],
      /// dispatches next recursive call.
      struct _After_QNode_2 {
        T1 _result_0;
        T1 _result_1;
        const qtree *_s2;
        qtree a4;
        qtree a3;
        unsigned int a2;
        qtree a1;
        qtree a0;
      };

      /// _Combine_QNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_QNode {
        T1 _result_0;
        T1 _result_1;
        T1 _result_2;
        qtree a4;
        qtree a3;
        unsigned int a2;
        qtree a1;
        qtree a0;
      };

      using _Frame = std::variant<_Enter, _After_QNode, _After_QNode_1,
                                  _After_QNode_2, _Combine_QNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified qtree_rect: _Enter -> _After_QNode -> _After_QNode_1 ->
      /// _After_QNode_2 -> _Combine_QNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const qtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename qtree::QLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename qtree::QNode>(_sv.v());
            _stack.emplace_back(_After_QNode{a3.get(), a1.get(), a0.get(), *a4,
                                             *a3, a2, *a1, *a0});
            _stack.emplace_back(_Enter{a4.get()});
          }
        } else if (std::holds_alternative<_After_QNode>(_frame)) {
          auto _f = std::move(std::get<_After_QNode>(_frame));
          _stack.emplace_back(_After_QNode_1{
              _result, _f._s1, _f._s2, std::move(_f.a4), std::move(_f.a3),
              _f.a2, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_After_QNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_1>(_frame));
          _stack.emplace_back(_After_QNode_2{
              _f._result, _result, _f._s2, std::move(_f.a4), std::move(_f.a3),
              _f.a2, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_After_QNode_2>(_frame)) {
          auto _f = std::move(std::get<_After_QNode_2>(_frame));
          _stack.emplace_back(_Combine_QNode{
              _f._result_0, _f._result_1, _result, std::move(_f.a4),
              std::move(_f.a3), _f.a2, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Combine_QNode>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result_2, _f.a2, _f.a3,
                       _f._result_1, _f.a4, _f._result_0);
        }
      }
      return _result;
    }
  };

  /// TEST 1: Sum of a 4-ary tree. Basic correctness.
  static inline const unsigned int test_qtree_sum = []() {
    qtree t = qtree::qnode(qtree::qnode(qtree::qleaf(), qtree::qleaf(), 1u,
                                        qtree::qleaf(), qtree::qleaf()),
                           qtree::qnode(qtree::qleaf(), qtree::qleaf(), 2u,
                                        qtree::qleaf(), qtree::qleaf()),
                           10u,
                           qtree::qnode(qtree::qleaf(), qtree::qleaf(), 3u,
                                        qtree::qleaf(), qtree::qleaf()),
                           qtree::qnode(qtree::qleaf(), qtree::qleaf(), 4u,
                                        qtree::qleaf(), qtree::qleaf()));
    return std::move(t).qtree_sum();
  }();
  /// TEST 2: Depth of a deep 4-ary tree.
  static inline const unsigned int test_qtree_depth = []() {
    qtree inner = qtree::qnode(qtree::qleaf(), qtree::qleaf(), 1u,
                               qtree::qleaf(), qtree::qleaf());
    qtree t = qtree::qnode(
        inner,
        qtree::qnode(inner, qtree::qleaf(), 2u, qtree::qleaf(), qtree::qleaf()),
        3u, qtree::qleaf(), qtree::qleaf());
    return std::move(t).qtree_depth();
  }();
  static inline const unsigned int test_qtree_mirror = []() {
    qtree t = qtree::qnode(qtree::qnode(qtree::qleaf(), qtree::qleaf(), 1u,
                                        qtree::qleaf(), qtree::qleaf()),
                           qtree::qleaf(), 10u,
                           qtree::qnode(qtree::qleaf(), qtree::qleaf(), 3u,
                                        qtree::qleaf(), qtree::qleaf()),
                           qtree::qleaf());
    return std::move(t).qtree_mirror().qtree_sum();
  }();

  /// TEST 4: Flatten a 4-ary tree to a list (inorder traversal).
  /// Uses all 4 children in recursive calls + value in list construction.
  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::unique_ptr<mylist<A>> a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : v_(_v) {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    mylist(const mylist<A> &_other) : v_(std::move(_other.clone().v_)) {}

    mylist(mylist<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    mylist<A> &operator=(const mylist<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist<A> &operator=(mylist<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    mylist<A> clone() const {
      mylist<A> _out{};

      struct _CloneFrame {
        const mylist<A> *_src;
        mylist<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist<A> *_src = _frame._src;
        mylist<A> *_dst = _frame._dst;
        if (std::holds_alternative<Mynil>(_src->v())) {
          _dst->v_ = Mynil{};
        } else {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->v_ = Mycons{_alt.a0,
                            _alt.a1 ? std::make_unique<mylist<A>>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ =
            Mycons{A(a0), a1 ? std::make_unique<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> mynil() { return mylist(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mylist<A> &_node) {
        if (std::holds_alternative<Mycons>(_node.v_)) {
          auto &_alt = std::get<Mycons>(_node.v_);
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

    mylist<A> myapp(mylist<A> l2) const {
      std::unique_ptr<mylist<A>> _head{};
      std::unique_ptr<mylist<A>> *_write = &_head;
      const mylist *_loop_self = this;
      mylist<A> _loop_l2 = std::move(l2);
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
          *_write = std::make_unique<mylist<A>>(std::move(_loop_l2));
          break;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(_sv.v());
          auto _cell = std::make_unique<mylist<A>>(
              typename mylist<A>::Mycons(a0, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename mylist<A>::Mycons>((*_write)->v_mut()).a1;
          _loop_self = a1.get();
          continue;
        }
      }
      return std::move(*_head);
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [f0, a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        F1 f0;
        mylist<A> a1;
        A a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rec: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{f0, *a1, a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = _f.f0(_f.a0, _f.a1, _result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [f0, a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        F1 f0;
        mylist<A> a1;
        A a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rect: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{f0, *a1, a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = _f.f0(_f.a0, _f.a1, _result);
        }
      }
      return _result;
    }
  };

  static unsigned int sum_list(const mylist<unsigned int> &l);
  static mylist<unsigned int> qtree_flatten(const qtree &t);
  static inline const unsigned int test_qtree_flatten = []() {
    qtree t = qtree::qnode(qtree::qnode(qtree::qleaf(), qtree::qleaf(), 1u,
                                        qtree::qleaf(), qtree::qleaf()),
                           qtree::qnode(qtree::qleaf(), qtree::qleaf(), 2u,
                                        qtree::qleaf(), qtree::qleaf()),
                           5u,
                           qtree::qnode(qtree::qleaf(), qtree::qleaf(), 3u,
                                        qtree::qleaf(), qtree::qleaf()),
                           qtree::qnode(qtree::qleaf(), qtree::qleaf(), 4u,
                                        qtree::qleaf(), qtree::qleaf()));
    return sum_list(qtree_flatten(std::move(t)));
  }();
  static inline const unsigned int test_qtree_zip = []() {
    qtree t1 = qtree::qnode(qtree::qleaf(), qtree::qleaf(), 10u, qtree::qleaf(),
                            qtree::qleaf());
    qtree t2 = qtree::qnode(qtree::qleaf(), qtree::qleaf(), 20u, qtree::qleaf(),
                            qtree::qleaf());
    return std::move(t1).qtree_zip(std::move(t2)).qtree_sum();
  }();
  static inline const unsigned int test_weighted = []() {
    qtree t = qtree::qnode(qtree::qnode(qtree::qleaf(), qtree::qleaf(), 1u,
                                        qtree::qleaf(), qtree::qleaf()),
                           qtree::qnode(qtree::qleaf(), qtree::qleaf(), 2u,
                                        qtree::qleaf(), qtree::qleaf()),
                           3u,
                           qtree::qnode(qtree::qleaf(), qtree::qleaf(), 4u,
                                        qtree::qleaf(), qtree::qleaf()),
                           qtree::qnode(qtree::qleaf(), qtree::qleaf(), 5u,
                                        qtree::qleaf(), qtree::qleaf()));
    return std::move(t).weighted_sum();
  }();
  /// TEST 7: Build a 4-ary tree programmatically and check.
  static qtree make_qtree(unsigned int n);
  static inline const unsigned int test_make_qtree = make_qtree(4u).qtree_sum();
  /// TEST 8: Two-pass on a 4-ary tree: flatten then sum vs direct sum.
  static inline const unsigned int test_two_pass_qtree = []() {
    qtree t = qtree::qnode(qtree::qnode(qtree::qleaf(), qtree::qleaf(), 1u,
                                        qtree::qleaf(), qtree::qleaf()),
                           qtree::qnode(qtree::qleaf(), qtree::qleaf(), 2u,
                                        qtree::qleaf(), qtree::qleaf()),
                           5u,
                           qtree::qnode(qtree::qleaf(), qtree::qleaf(), 3u,
                                        qtree::qleaf(), qtree::qleaf()),
                           qtree::qnode(qtree::qleaf(), qtree::qleaf(), 4u,
                                        qtree::qleaf(), qtree::qleaf()));
    return (sum_list(qtree_flatten(t)) + t.qtree_sum());
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE17
