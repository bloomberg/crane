#ifndef INCLUDED_SEPEXTSELFREFINDUCTIVE
#define INCLUDED_SEPEXTSELFREFINDUCTIVE

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <stdexcept>
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
      V v_1;
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

    template <typename CraneU>
    Trie(const Trie<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename Trie<CraneU>::Empty>(
                    _other.v())) {
              return Empty{};
            } else {
              const auto &[k, v_1, left, right] =
                  std::get<typename Trie<CraneU>::Node>(_other.v());
              return Node{
                  k,
                  [&]() -> V {
                    if constexpr (crane_convertible<V, const CraneU &>) {
                      return crane_convert<V>(v_1);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (left ? std::make_shared<Trie<V>>(
                              crane_convert<Trie<V>>(*left))
                        : nullptr),
                  (right ? std::make_shared<Trie<V>>(
                               crane_convert<Trie<V>>(*right))
                         : nullptr)};
            }
          }()) {}

    static Trie<V> empty() { return Trie<V>(Empty{}); }

    static Trie<V> node(typename X::t k, V v_1, Trie<V> left, Trie<V> right) {
      return Trie<V>(Node{std::move(k), std::move(v_1),
                          std::make_shared<Trie<V>>(std::move(left)),
                          std::make_shared<Trie<V>>(std::move(right))});
    }

    // MANIPULATORS
    ~Trie() {
      crane::small_vector<std::shared_ptr<Trie<V>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->left && _alt->left.use_count() == 1) {
            _stack.push_back(std::move(_alt->left));
          }
          if (_alt->right && _alt->right.use_count() == 1) {
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
    Trie(Trie &&) = default;
    Trie &operator=(Trie &&) = default;

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
      const auto &[k0, v_1, left0, right0] =
          std::get<typename Trie<T1>::Node>(t0.v());
      return f0(k0, v_1, *left0, Trie_rect<T1, T2>(f, f0, *left0), *right0,
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
      const auto &[k0, v_1, left0, right0] =
          std::get<typename Trie<T1>::Node>(t0.v());
      return f0(k0, v_1, *left0, Trie_rec<T1, T2>(f, f0, *left0), *right0,
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
