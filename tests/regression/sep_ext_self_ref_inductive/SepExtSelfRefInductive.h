#ifndef INCLUDED_SEPEXTSELFREFINDUCTIVE
#define INCLUDED_SEPEXTSELFREFINDUCTIVE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

namespace SepExtSelfRefInductive {

template <typename M>
concept S = requires { typename M::t; };

template <S X> struct HashTrie {
  template <typename V> struct Trie {
    // TYPES
    struct Empty {};

    struct Node {
      typename X::t k;
      V v;
      std::shared_ptr<Trie<V>> left;
      std::shared_ptr<Trie<V>> right;
    };

    using variant_t = std::variant<Empty, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Trie() {}

    explicit Trie(Empty _v) : v_(_v) {}

    explicit Trie(Node _v) : v_(std::move(_v)) {}

    template <typename _U> Trie(const Trie<_U> &_other) {
      if (std::holds_alternative<typename Trie<_U>::Empty>(_other.v())) {
        this->v_ = Empty{};
      } else {
        const auto &[k, v, left, right] =
            std::get<typename Trie<_U>::Node>(_other.v());
        this->v_ = Node{k,
                        [&]() -> V {
                          if constexpr (std::is_same_v<_U, std::any>)
                            return crane_any_cast<V>(v);
                          else
                            return V(v);
                        }(),
                        left ? std::make_shared<Trie<V>>(*left) : nullptr,
                        right ? std::make_shared<Trie<V>>(*right) : nullptr};
      }
    }

    static Trie<V> empty() { return Trie<V>(Empty{}); }

    static Trie<V> node(typename X::t k, V v, Trie<V> left, Trie<V> right) {
      return Trie<V>(Node{std::move(k), std::move(v),
                          std::make_shared<Trie<V>>(std::move(left)),
                          std::make_shared<Trie<V>>(std::move(right))});
    }

    // MANIPULATORS
    ~Trie() {
      crane::small_vector<std::shared_ptr<Trie<V>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->left) {
            _stack.push_back(std::move(_alt->left));
          }
          if (_alt->right) {
            _stack.push_back(std::move(_alt->right));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    Trie(const Trie &) = default;
    Trie &operator=(const Trie &) = default;
    Trie(Trie &&) noexcept = default;
    Trie &operator=(Trie &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, typename X::t &, T1 &, Trie<T1> &,
                                   T2 &, Trie<T1> &, T2 &>
  static T2 Trie_rect(T2 f, F1 &&f0, const Trie<T1> &t0) {
    if (std::holds_alternative<typename Trie<T1>::Empty>(t0.v())) {
      return f;
    } else {
      const auto &[k0, v0, left0, right0] =
          std::get<typename Trie<T1>::Node>(t0.v());
      return f0(k0, v0, *left0, Trie_rect<T1, T2>(f, f0, *left0), *right0,
                Trie_rect<T1, T2>(f, f0, *right0));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, typename X::t &, T1 &, Trie<T1> &,
                                   T2 &, Trie<T1> &, T2 &>
  static T2 Trie_rec(T2 f, F1 &&f0, const Trie<T1> &t0) {
    if (std::holds_alternative<typename Trie<T1>::Empty>(t0.v())) {
      return f;
    } else {
      const auto &[k0, v0, left0, right0] =
          std::get<typename Trie<T1>::Node>(t0.v());
      return f0(k0, v0, *left0, Trie_rec<T1, T2>(f, f0, *left0), *right0,
                Trie_rec<T1, T2>(f, f0, *right0));
    }
  }

  template <typename T1> static const Trie<T1> &empty() {
    static const Trie<T1> v = Trie<T1>::empty();
    return v;
  }

  template <typename T1> static bool is_empty(const Trie<T1> &t0) {
    if (std::holds_alternative<typename Trie<T1>::Empty>(t0.v())) {
      return true;
    } else {
      return false;
    }
  }
};

} // namespace SepExtSelfRefInductive

#endif // INCLUDED_SEPEXTSELFREFINDUCTIVE
