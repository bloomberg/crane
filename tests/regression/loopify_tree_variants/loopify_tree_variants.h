#ifndef INCLUDED_LOOPIFY_TREE_VARIANTS
#define INCLUDED_LOOPIFY_TREE_VARIANTS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct LoopifyTreeVariants {
  struct ternary {
    // TYPES
    struct TLeaf {};

    struct TNode {
      std::shared_ptr<ternary> d_a0;
      unsigned int d_a1;
      std::shared_ptr<ternary> d_a2;
      std::shared_ptr<ternary> d_a3;
    };

    using variant_t = std::variant<TLeaf, TNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit ternary(TLeaf _v) : d_v_(_v) {}

    explicit ternary(TNode _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<ternary> tleaf() {
      return std::make_shared<ternary>(TLeaf{});
    }

    static std::shared_ptr<ternary> tnode(const std::shared_ptr<ternary> &a0,
                                          unsigned int a1,
                                          const std::shared_ptr<ternary> &a2,
                                          const std::shared_ptr<ternary> &a3) {
      return std::make_shared<ternary>(TNode{a0, std::move(a1), a2, a3});
    }

    static std::shared_ptr<ternary> tnode(std::shared_ptr<ternary> &&a0,
                                          unsigned int a1,
                                          std::shared_ptr<ternary> &&a2,
                                          std::shared_ptr<ternary> &&a3) {
      return std::make_shared<ternary>(
          TNode{std::move(a0), std::move(a1), std::move(a2), std::move(a3)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

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
          const auto &_f = std::get<_Enter>(_frame);
          const ternary *_self = _f._self;
          if (std::holds_alternative<typename ternary::TLeaf>(_self->v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename ternary::TNode>(_self->v());
            _stack.emplace_back(_Call1{d_a2.get(), d_a0.get(), 1u});
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
        } else {
          const auto &_f = std::get<_Call3>(_frame);
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
          const auto &_f = std::get<_Enter>(_frame);
          const ternary *_self = _f._self;
          if (std::holds_alternative<typename ternary::TLeaf>(_self->v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename ternary::TNode>(_self->v());
            _stack.emplace_back(_Call1{d_a2.get(), d_a0.get(), d_a1});
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
        } else {
          const auto &_f = std::get<_Call3>(_frame);
          _result = (((_result + _f._s2) + _f._s1) + _f._s0);
        }
      }
      return _result;
    }

    template <typename T1,
              MapsTo<T1, std::shared_ptr<ternary>, T1, unsigned int,
                     std::shared_ptr<ternary>, T1, std::shared_ptr<ternary>, T1>
                  F1>
    T1 ternary_rec(const T1 f, F1 &&f0) const {
      const ternary *_self = this;

      struct _Enter {
        const ternary *_self;
      };

      struct _Call1 {
        const ternary *_s0;
        const ternary *_s1;
        std::shared_ptr<ternary> _s2;
        std::shared_ptr<ternary> _s3;
        unsigned int _s4;
        std::shared_ptr<ternary> _s5;
      };

      struct _Call2 {
        T1 _s0;
        const ternary *_s1;
        std::shared_ptr<ternary> _s2;
        std::shared_ptr<ternary> _s3;
        unsigned int _s4;
        std::shared_ptr<ternary> _s5;
      };

      struct _Call3 {
        T1 _s0;
        T1 _s1;
        std::shared_ptr<ternary> _s2;
        std::shared_ptr<ternary> _s3;
        unsigned int _s4;
        std::shared_ptr<ternary> _s5;
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
          const auto &_f = std::get<_Enter>(_frame);
          const ternary *_self = _f._self;
          if (std::holds_alternative<typename ternary::TLeaf>(_self->v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename ternary::TNode>(_self->v());
            _stack.emplace_back(
                _Call1{d_a2.get(), d_a0.get(), d_a3, d_a2, d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(
              _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _stack.emplace_back(
              _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          const auto &_f = std::get<_Call3>(_frame);
          _result = f0(_f._s5, _result, _f._s4, _f._s3, _f._s1, _f._s2, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1,
              MapsTo<T1, std::shared_ptr<ternary>, T1, unsigned int,
                     std::shared_ptr<ternary>, T1, std::shared_ptr<ternary>, T1>
                  F1>
    T1 ternary_rect(const T1 f, F1 &&f0) const {
      const ternary *_self = this;

      struct _Enter {
        const ternary *_self;
      };

      struct _Call1 {
        const ternary *_s0;
        const ternary *_s1;
        std::shared_ptr<ternary> _s2;
        std::shared_ptr<ternary> _s3;
        unsigned int _s4;
        std::shared_ptr<ternary> _s5;
      };

      struct _Call2 {
        T1 _s0;
        const ternary *_s1;
        std::shared_ptr<ternary> _s2;
        std::shared_ptr<ternary> _s3;
        unsigned int _s4;
        std::shared_ptr<ternary> _s5;
      };

      struct _Call3 {
        T1 _s0;
        T1 _s1;
        std::shared_ptr<ternary> _s2;
        std::shared_ptr<ternary> _s3;
        unsigned int _s4;
        std::shared_ptr<ternary> _s5;
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
          const auto &_f = std::get<_Enter>(_frame);
          const ternary *_self = _f._self;
          if (std::holds_alternative<typename ternary::TLeaf>(_self->v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename ternary::TNode>(_self->v());
            _stack.emplace_back(
                _Call1{d_a2.get(), d_a0.get(), d_a3, d_a2, d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(
              _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          const auto &_f = std::get<_Call2>(_frame);
          _stack.emplace_back(
              _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          const auto &_f = std::get<_Call3>(_frame);
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
          _result = (((_result + _f._s2) + _f._s1) + _f._s0);
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

  struct leaf_tree {
    // TYPES
    struct LLeaf {
      unsigned int d_a0;
    };

    struct LNode {
      std::shared_ptr<leaf_tree> d_a0;
      std::shared_ptr<leaf_tree> d_a1;
    };

    using variant_t = std::variant<LLeaf, LNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit leaf_tree(LLeaf _v) : d_v_(std::move(_v)) {}

    explicit leaf_tree(LNode _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<leaf_tree> lleaf(unsigned int a0) {
      return std::make_shared<leaf_tree>(LLeaf{std::move(a0)});
    }

    static std::shared_ptr<leaf_tree>
    lnode(const std::shared_ptr<leaf_tree> &a0,
          const std::shared_ptr<leaf_tree> &a1) {
      return std::make_shared<leaf_tree>(LNode{a0, a1});
    }

    static std::shared_ptr<leaf_tree> lnode(std::shared_ptr<leaf_tree> &&a0,
                                            std::shared_ptr<leaf_tree> &&a1) {
      return std::make_shared<leaf_tree>(LNode{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int leaf_tree_max() const {
      const leaf_tree *_self = this;

      struct _Enter {
        const leaf_tree *_self;
      };

      struct _Call1 {
        std::shared_ptr<leaf_tree> _s0;
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
          const auto &_f = std::get<_Enter>(_frame);
          const leaf_tree *_self = _f._self;
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_self->v())) {
            const auto &[d_a0] =
                std::get<typename leaf_tree::LLeaf>(_self->v());
            _result = d_a0;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename leaf_tree::LNode>(_self->v());
            _stack.emplace_back(_Call1{d_a1});
            _stack.emplace_back(_Enter{d_a0.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          std::shared_ptr<leaf_tree> d_a1 = _f._s0;
          unsigned int lmax = _result;
          _stack.emplace_back(_Call2{lmax});
          _stack.emplace_back(_Enter{d_a1.get()});
        } else {
          const auto &_f = std::get<_Call2>(_frame);
          unsigned int lmax = _f._s0;
          unsigned int rmax = _result;
          if (lmax < rmax) {
            _result = rmax;
          } else {
            _result = lmax;
          }
        }
      }
      return _result;
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
          const auto &_f = std::get<_Enter>(_frame);
          const leaf_tree *_self = _f._self;
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_self->v())) {
            const auto &[d_a0] =
                std::get<typename leaf_tree::LLeaf>(_self->v());
            _result = d_a0;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename leaf_tree::LNode>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call2>(_frame);
          _result = (_result + _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<leaf_tree>, T1,
                     std::shared_ptr<leaf_tree>, T1>
                  F1>
    T1 leaf_tree_rec(F0 &&f, F1 &&f0) const {
      const leaf_tree *_self = this;

      struct _Enter {
        const leaf_tree *_self;
      };

      struct _Call1 {
        leaf_tree *_s0;
        std::shared_ptr<leaf_tree> _s1;
        std::shared_ptr<leaf_tree> _s2;
      };

      struct _Call2 {
        T1 _s0;
        std::shared_ptr<leaf_tree> _s1;
        std::shared_ptr<leaf_tree> _s2;
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
          const leaf_tree *_self = _f._self;
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_self->v())) {
            const auto &[d_a0] =
                std::get<typename leaf_tree::LLeaf>(_self->v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename leaf_tree::LNode>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call2>(_frame);
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<leaf_tree>, T1,
                     std::shared_ptr<leaf_tree>, T1>
                  F1>
    T1 leaf_tree_rect(F0 &&f, F1 &&f0) const {
      const leaf_tree *_self = this;

      struct _Enter {
        const leaf_tree *_self;
      };

      struct _Call1 {
        leaf_tree *_s0;
        std::shared_ptr<leaf_tree> _s1;
        std::shared_ptr<leaf_tree> _s2;
      };

      struct _Call2 {
        T1 _s0;
        std::shared_ptr<leaf_tree> _s1;
        std::shared_ptr<leaf_tree> _s2;
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
          const leaf_tree *_self = _f._self;
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_self->v())) {
            const auto &[d_a0] =
                std::get<typename leaf_tree::LLeaf>(_self->v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename leaf_tree::LNode>(_self->v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a1, d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          const auto &_f = std::get<_Call1>(_frame);
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          const auto &_f = std::get<_Call2>(_frame);
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_TREE_VARIANTS
