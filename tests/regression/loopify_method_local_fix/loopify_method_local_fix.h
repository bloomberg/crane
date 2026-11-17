#pragma once

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

struct LoopifyMethodLocalFix {
  struct Tree {
    struct tree {
      // TYPES
      struct Leaf {};

      struct Node {
        std::shared_ptr<tree> a0;
        uint64_t a1;
      };

      using variant_t = std::variant<Leaf, Node>;

    private:
      // DATA
      variant_t v_;

    public:
      // CREATORS
      tree() {}

      explicit tree(Leaf _v) : v_(_v) {}

      explicit tree(Node _v) : v_(std::move(_v)) {}

      static tree leaf() { return tree(Leaf{}); }

      static tree node(crane::shared_child_slot<tree> a0, uint64_t a1) {
        return tree(Node{a0.take(), a1});
      }

      // MANIPULATORS
      ~tree() {
        // Release the children this node alone owns in a loop, not recursively,
        // so a deep value cannot overflow the stack.
        auto _next = [&](variant_t &_v) -> std::shared_ptr<tree> {
          if (auto *_alt = std::get_if<Node>(&_v)) {
            if (_alt->a0 && _alt->a0.use_count() == 1) {
              std::atomic_thread_fence(std::memory_order_acquire);
              return std::move(_alt->a0);
            }
          }
          return nullptr;
        };
        std::shared_ptr<tree> _cur = _next(v_mut());
        while (_cur) {
          _cur = _next(_cur->v_mut());
        }
      }

      tree(const tree &) = default;
      tree &operator=(const tree &) = default;
      tree(tree &&) = default;
      tree &operator=(tree &&) = default;

      inline variant_t &v_mut() { return v_; }

      // ACCESSORS
      const variant_t &v() const { return v_; }

      template <typename T1, typename F1> T1 tree_rect(T1 f, F1 &&f0) const {
        const tree *_self = this;

        // Explicit stack replaces the non-tail recursion of tree_rect: _call
        // frames are pending calls, _after frames resume a caller.
        struct _call {
          const tree *_self;
        };

        struct _after_tree_rect_in_Node {
          std::shared_ptr<tree> a0;
          uint64_t a1;
        };

        using _frame = std::variant<_call, _after_tree_rect_in_Node>;
        T1 _result{};
        crane::small_vector<_frame> _stack;
        _stack.emplace_back(_call{_self});
        while (!_stack.empty()) {
          _frame &_popped = _stack.back();
          if (std::holds_alternative<_call>(_popped)) {
            auto _f = std::move(std::get<_call>(_popped));
            _stack.pop_back();
            const tree *_self = _f._self;
            auto &&_sv = *_self;
            if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
              _result = f;
            } else {
              const auto &[a0, a1] = std::get<typename tree::Node>(_sv.v());
              _stack.emplace_back(_after_tree_rect_in_Node{a0, a1});
              _stack.emplace_back(_call{crane_raw(a0)});
            }
          } else {
            auto _f = std::move(std::get<_after_tree_rect_in_Node>(_popped));
            _stack.pop_back();
            std::shared_ptr<tree> a0 = std::move(_f.a0);
            uint64_t a1 = _f.a1;
            _result = f0(*a0, std::move(_result), a1);
          }
        }
        return _result;
      }

      template <typename T1, typename F1> T1 tree_rec(T1 f, F1 &&f0) const {
        return this->template tree_rect<T1>(std::move(f), f0);
      }

      uint64_t drain(uint64_t n) const {
        // Loop replaces the tail recursion: each recursive call updates the
        // loop variables.
        const tree *_loop_self = this;
        uint64_t _loop_n = n;
        while (true) {
          auto &&_sv = *_loop_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            auto go = [](uint64_t k, uint64_t acc) -> uint64_t {
              // Loop replaces the tail recursion: each recursive call updates
              // the loop variables.
              uint64_t _loop_acc = acc;
              uint64_t _loop_k = k;
              while (true) {
                if (_loop_k <= 0) {
                  return _loop_acc;
                } else {
                  uint64_t k_ = _loop_k - 1;
                  _loop_acc = (_loop_acc + 1);
                  _loop_k = k_;
                }
              }
            };
            return go(_loop_n, UINT64_C(0));
          } else {
            const auto &[a0, a1] = std::get<typename tree::Node>(_sv.v());
            _loop_self = crane_raw(a0);
            _loop_n = (_loop_n + a1);
          }
        }
      }
    };
  };
};
