#ifndef INCLUDED_LOOPIFY_TREE_VARIANTS
#define INCLUDED_LOOPIFY_TREE_VARIANTS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
    __attribute__((pure)) ternary clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<TLeaf>(_sv.v())) {
        return ternary(TLeaf{});
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3] = std::get<TNode>(_sv.v());
        return ternary(TNode{
            d_a0 ? std::make_unique<LoopifyTreeVariants::ternary>(d_a0->clone())
                 : nullptr,
            d_a1,
            d_a2 ? std::make_unique<LoopifyTreeVariants::ternary>(d_a2->clone())
                 : nullptr,
            d_a3 ? std::make_unique<LoopifyTreeVariants::ternary>(d_a3->clone())
                 : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static ternary tleaf() { return ternary(TLeaf{}); }

    __attribute__((pure)) static ternary tnode(ternary a0, unsigned int a1,
                                               ternary a2, ternary a3) {
      return ternary(TNode{std::make_unique<ternary>(std::move(a0)),
                           std::move(a1),
                           std::make_unique<ternary>(std::move(a2)),
                           std::make_unique<ternary>(std::move(a3))});
    }

    // MANIPULATORS
    ~ternary() {
      std::vector<std::unique_ptr<ternary>> _stack;
      auto _drain = [&](ternary &_node) {
        if (std::holds_alternative<TNode>(_node.d_v_)) {
          auto &_alt = std::get<TNode>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a2)
            _stack.push_back(std::move(_alt.d_a2));
          if (_alt.d_a3)
            _stack.push_back(std::move(_alt.d_a3));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int ternary_count() const {
      const ternary *_self = this;

      struct _Enter {
        const ternary *_self;
      };

      struct _Call1 {
        const ternary *_s0;
        const ternary *_s1;
        decltype(1u) _s2;
      };

      struct _Call2 {
        unsigned int _s0;
        const ternary *_s1;
        decltype(1u) _s2;
      };

      struct _Call3 {
        unsigned int _s0;
        unsigned int _s1;
        decltype(1u) _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
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
            _stack.emplace_back(_Call1{d_a2.get(), d_a0.get(), 1u});
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
        } else {
          auto _f = std::move(std::get<_Call3>(_frame));
          _result = (((_f._s2 + _result) + _f._s1) + _f._s0);
        }
      }
      return _result;
    }

    __attribute__((pure)) unsigned int ternary_sum() const {
      const ternary *_self = this;

      struct _Enter {
        const ternary *_self;
      };

      struct _Call1 {
        const ternary *_s0;
        const ternary *_s1;
        unsigned int _s2;
      };

      struct _Call2 {
        unsigned int _s0;
        const ternary *_s1;
        unsigned int _s2;
      };

      struct _Call3 {
        unsigned int _s0;
        unsigned int _s1;
        unsigned int _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
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
            _stack.emplace_back(_Call1{d_a2.get(), d_a0.get(), d_a1});
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
        } else {
          auto _f = std::move(std::get<_Call3>(_frame));
          _result = (((_result + _f._s2) + _f._s1) + _f._s0);
        }
      }
      return _result;
    }

    template <
        typename T1,
        MapsTo<T1, ternary, T1, unsigned int, ternary, T1, ternary, T1> F1>
    T1 ternary_rec(const T1 f, F1 &&f0) const {
      const ternary *_self = this;

      struct _Enter {
        const ternary *_self;
      };

      struct _Call1 {
        const ternary *_s0;
        const ternary *_s1;
        ternary _s2;
        ternary _s3;
        unsigned int _s4;
        ternary _s5;
      };

      struct _Call2 {
        T1 _s0;
        const ternary *_s1;
        ternary _s2;
        ternary _s3;
        unsigned int _s4;
        ternary _s5;
      };

      struct _Call3 {
        T1 _s0;
        T1 _s1;
        ternary _s2;
        ternary _s3;
        unsigned int _s4;
        ternary _s5;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
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
            _stack.emplace_back(_Call1{d_a2.get(), d_a0.get(), *(d_a3), *(d_a2),
                                       d_a1, *(d_a0)});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(
              _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(
              _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call3>(_frame));
          _result = f0(_f._s5, _result, _f._s4, _f._s3, _f._s1, _f._s2, _f._s0);
        }
      }
      return _result;
    }

    template <
        typename T1,
        MapsTo<T1, ternary, T1, unsigned int, ternary, T1, ternary, T1> F1>
    T1 ternary_rect(const T1 f, F1 &&f0) const {
      const ternary *_self = this;

      struct _Enter {
        const ternary *_self;
      };

      struct _Call1 {
        const ternary *_s0;
        const ternary *_s1;
        ternary _s2;
        ternary _s3;
        unsigned int _s4;
        ternary _s5;
      };

      struct _Call2 {
        T1 _s0;
        const ternary *_s1;
        ternary _s2;
        ternary _s3;
        unsigned int _s4;
        ternary _s5;
      };

      struct _Call3 {
        T1 _s0;
        T1 _s1;
        ternary _s2;
        ternary _s3;
        unsigned int _s4;
        ternary _s5;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
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
            _stack.emplace_back(_Call1{d_a2.get(), d_a0.get(), *(d_a3), *(d_a2),
                                       d_a1, *(d_a0)});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(
              _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(
              _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call3>(_frame));
          _result = f0(_f._s5, _result, _f._s4, _f._s3, _f._s1, _f._s2, _f._s0);
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
    __attribute__((pure)) quadtree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<QLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<QLeaf>(_sv.v());
        return quadtree(QLeaf{d_a0});
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3] = std::get<Quad>(_sv.v());
        return quadtree(Quad{
            d_a0
                ? std::make_unique<LoopifyTreeVariants::quadtree>(d_a0->clone())
                : nullptr,
            d_a1
                ? std::make_unique<LoopifyTreeVariants::quadtree>(d_a1->clone())
                : nullptr,
            d_a2
                ? std::make_unique<LoopifyTreeVariants::quadtree>(d_a2->clone())
                : nullptr,
            d_a3
                ? std::make_unique<LoopifyTreeVariants::quadtree>(d_a3->clone())
                : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static quadtree qleaf(unsigned int a0) {
      return quadtree(QLeaf{std::move(a0)});
    }

    __attribute__((pure)) static quadtree quad(quadtree a0, quadtree a1,
                                               quadtree a2, quadtree a3) {
      return quadtree(Quad{std::make_unique<quadtree>(std::move(a0)),
                           std::make_unique<quadtree>(std::move(a1)),
                           std::make_unique<quadtree>(std::move(a2)),
                           std::make_unique<quadtree>(std::move(a3))});
    }

    // MANIPULATORS
    ~quadtree() {
      std::vector<std::unique_ptr<quadtree>> _stack;
      auto _drain = [&](quadtree &_node) {
        if (std::holds_alternative<Quad>(_node.d_v_)) {
          auto &_alt = std::get<Quad>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
          if (_alt.d_a2)
            _stack.push_back(std::move(_alt.d_a2));
          if (_alt.d_a3)
            _stack.push_back(std::move(_alt.d_a3));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

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
          _result = (((_result + _f._s2) + _f._s1) + _f._s0);
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
    __attribute__((pure)) leaf_tree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<LLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<LLeaf>(_sv.v());
        return leaf_tree(LLeaf{d_a0});
      } else {
        const auto &[d_a0, d_a1] = std::get<LNode>(_sv.v());
        return leaf_tree(
            LNode{d_a0 ? std::make_unique<LoopifyTreeVariants::leaf_tree>(
                             d_a0->clone())
                       : nullptr,
                  d_a1 ? std::make_unique<LoopifyTreeVariants::leaf_tree>(
                             d_a1->clone())
                       : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static leaf_tree lleaf(unsigned int a0) {
      return leaf_tree(LLeaf{std::move(a0)});
    }

    __attribute__((pure)) static leaf_tree lnode(leaf_tree a0, leaf_tree a1) {
      return leaf_tree(LNode{std::make_unique<leaf_tree>(std::move(a0)),
                             std::make_unique<leaf_tree>(std::move(a1))});
    }

    // MANIPULATORS
    ~leaf_tree() {
      std::vector<std::unique_ptr<leaf_tree>> _stack;
      auto _drain = [&](leaf_tree &_node) {
        if (std::holds_alternative<LNode>(_node.d_v_)) {
          auto &_alt = std::get<LNode>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int leaf_tree_max() const {
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

    __attribute__((pure)) unsigned int leaf_tree_sum() const {
      const leaf_tree *_self = this;

      struct _Enter {
        const leaf_tree *_self;
      };

      struct _Call1 {
        leaf_tree *_s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
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
            _stack.emplace_back(_Call1{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = (_result + _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, leaf_tree, T1, leaf_tree, T1> F1>
    T1 leaf_tree_rec(F0 &&f, F1 &&f0) const {
      const leaf_tree *_self = this;

      struct _Enter {
        const leaf_tree *_self;
      };

      struct _Call1 {
        leaf_tree *_s0;
        leaf_tree _s1;
        leaf_tree _s2;
      };

      struct _Call2 {
        T1 _s0;
        leaf_tree _s1;
        leaf_tree _s2;
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
          const leaf_tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename leaf_tree::LLeaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename leaf_tree::LNode>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, leaf_tree, T1, leaf_tree, T1> F1>
    T1 leaf_tree_rect(F0 &&f, F1 &&f0) const {
      const leaf_tree *_self = this;

      struct _Enter {
        const leaf_tree *_self;
      };

      struct _Call1 {
        leaf_tree *_s0;
        leaf_tree _s1;
        leaf_tree _s2;
      };

      struct _Call2 {
        T1 _s0;
        leaf_tree _s1;
        leaf_tree _s2;
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
          const leaf_tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename leaf_tree::LLeaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename leaf_tree::LNode>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_TREE_VARIANTS
