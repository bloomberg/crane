#ifndef INCLUDED_LOOPIFY_METHOD
#define INCLUDED_LOOPIFY_METHOD

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Tree {
  struct tree {
    // TYPES
    struct Leaf {
      unsigned int d_a0;
    };

    struct Node {
      unsigned int d_a0;
      std::shared_ptr<tree> d_a1;
      std::shared_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<tree> Leaf_(unsigned int a0) {
        return std::shared_ptr<tree>(new tree(Leaf{a0}));
      }

      static std::shared_ptr<tree> Node_(unsigned int a0,
                                         const std::shared_ptr<tree> &a1,
                                         const std::shared_ptr<tree> &a2) {
        return std::shared_ptr<tree>(new tree(Node{a0, a1, a2}));
      }

      static std::unique_ptr<tree> Leaf_uptr(unsigned int a0) {
        return std::unique_ptr<tree>(new tree(Leaf{a0}));
      }

      static std::unique_ptr<tree> Node_uptr(unsigned int a0,
                                             const std::shared_ptr<tree> &a1,
                                             const std::shared_ptr<tree> &a2) {
        return std::unique_ptr<tree>(new tree(Node{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, std::shared_ptr<tree>, T1,
                     std::shared_ptr<tree>, T1>
                  F1>
    T1 tree_rect(F0 &&f, F1 &&f0) const {
      struct _Enter {
        F0 f;
        F1 f0;
      };

      using _Frame = std::variant<_Enter>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{f, f0});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{[&](_Enter _f) {
              F0 f = _f.f;
              F1 f0 = _f.f0;
              std::visit(
                  Overloaded{[&](const typename tree::Leaf _args) -> T1 {
                               _result = f(_args.d_a0);
                               return {};
                             },
                             [&](const typename tree::Node _args) -> T1 {
                               _result = f0(
                                   _args.d_a0, _args.d_a1,
                                   _args.d_a1->template tree_rect<T1>(f, f0),
                                   _args.d_a2,
                                   _args.d_a2->template tree_rect<T1>(f, f0));
                               return {};
                             }},
                  this->v());
            }},
            _frame);
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, std::shared_ptr<tree>, T1,
                     std::shared_ptr<tree>, T1>
                  F1>
    T1 tree_rec(F0 &&f, F1 &&f0) const {
      struct _Enter {
        F0 f;
        F1 f0;
      };

      using _Frame = std::variant<_Enter>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{f, f0});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{[&](_Enter _f) {
              F0 f = _f.f;
              F1 f0 = _f.f0;
              std::visit(
                  Overloaded{[&](const typename tree::Leaf _args) -> T1 {
                               _result = f(_args.d_a0);
                               return {};
                             },
                             [&](const typename tree::Node _args) -> T1 {
                               _result =
                                   f0(_args.d_a0, _args.d_a1,
                                      _args.d_a1->template tree_rec<T1>(f, f0),
                                      _args.d_a2,
                                      _args.d_a2->template tree_rec<T1>(f, f0));
                               return {};
                             }},
                  this->v());
            }},
            _frame);
      }
      return _result;
    }

    __attribute__((pure)) unsigned int tree_sum() const {
      struct _Enter {};

      using _Frame = std::variant<_Enter>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{[&](_Enter _f) {
              std::visit(
                  Overloaded{
                      [&](const typename tree::Leaf _args) -> unsigned int {
                        _result = _args.d_a0;
                        return {};
                      },
                      [&](const typename tree::Node _args) -> unsigned int {
                        _result = (_args.d_a0 + (_args.d_a1->tree_sum() +
                                                 _args.d_a2->tree_sum()));
                        return {};
                      }},
                  this->v());
            }},
            _frame);
      }
      return _result;
    }

    __attribute__((pure)) unsigned int depth() const {
      struct _Enter {};

      using _Frame = std::variant<_Enter>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{[&](_Enter _f) {
              std::visit(
                  Overloaded{
                      [&](const typename tree::Leaf _args) -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename tree::Node _args) -> unsigned int {
                        _result = (std::max(_args.d_a1->depth(),
                                            _args.d_a2->depth()) +
                                   1);
                        return {};
                      }},
                  this->v());
            }},
            _frame);
      }
      return _result;
    }

    std::shared_ptr<tree> mirror() const {
      struct _Enter {};

      using _Frame = std::variant<_Enter>;
      std::shared_ptr<tree> _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(Overloaded{[&](_Enter _f) {
                     std::visit(
                         Overloaded{[&](const typename tree::Leaf _args)
                                        -> std::shared_ptr<tree> {
                                      _result = tree::ctor::Leaf_(_args.d_a0);
                                      return {};
                                    },
                                    [&](const typename tree::Node _args)
                                        -> std::shared_ptr<tree> {
                                      _result = tree::ctor::Node_(
                                          _args.d_a0, _args.d_a2->mirror(),
                                          _args.d_a1->mirror());
                                      return {};
                                    }},
                         this->v());
                   }},
                   _frame);
      }
      return _result;
    }

    __attribute__((pure)) unsigned int count_leaves() const {
      struct _Enter {};

      using _Frame = std::variant<_Enter>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{[&](_Enter _f) {
              std::visit(
                  Overloaded{
                      [&](const typename tree::Leaf _args) -> unsigned int {
                        _result = 1u;
                        return {};
                      },
                      [&](const typename tree::Node _args) -> unsigned int {
                        _result = (_args.d_a1->count_leaves() +
                                   _args.d_a2->count_leaves());
                        return {};
                      }},
                  this->v());
            }},
            _frame);
      }
      return _result;
    }

    __attribute__((pure)) unsigned int tree_max() const {
      struct _Enter {};

      using _Frame = std::variant<_Enter>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{[&](_Enter _f) {
              std::visit(
                  Overloaded{
                      [&](const typename tree::Leaf _args) -> unsigned int {
                        _result = _args.d_a0;
                        return {};
                      },
                      [&](const typename tree::Node _args) -> unsigned int {
                        _result = std::max(_args.d_a0,
                                           std::max(_args.d_a1->tree_max(),
                                                    _args.d_a2->tree_max()));
                        return {};
                      }},
                  this->v());
            }},
            _frame);
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_METHOD
