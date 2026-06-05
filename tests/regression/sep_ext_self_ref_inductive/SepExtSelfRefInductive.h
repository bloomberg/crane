#ifndef INCLUDED_SEPEXTSELFREFINDUCTIVE
#define INCLUDED_SEPEXTSELFREFINDUCTIVE

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

    template <typename _U> explicit Trie(const Trie<_U> &_other) {
      if (std::holds_alternative<typename Trie<_U>::Empty>(_other.v())) {
        this->v_ = Empty{};
      } else {
        const auto &[k, v, left, right] =
            std::get<typename Trie<_U>::Node>(_other.v());
        this->v_ = Node{
            k,
            [&]() -> V {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (v.type() == typeid(V))
                  return std::any_cast<V>(v);
                if constexpr (requires {
                                typename V::first_type;
                                typename V::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(v);
                  return V{
                      [&]() -> typename V::first_type {
                        if constexpr (std::is_same_v<typename V::first_type,
                                                     std::any>)
                          return _k;
                        else
                          return std::any_cast<typename V::first_type>(_k);
                      }(),
                      [&]() -> typename V::second_type {
                        if constexpr (std::is_same_v<typename V::second_type,
                                                     std::any>)
                          return _v;
                        else
                          return std::any_cast<typename V::second_type>(_v);
                      }()};
                }
                return std::any_cast<V>(v);
              } else
                return V(v);
            }(),
            left ? std::make_shared<Trie<V>>(*left) : nullptr,
            right ? std::make_shared<Trie<V>>(*right) : nullptr};
      }
    }

    static Trie<V> empty() { return Trie(Empty{}); }

    static Trie<V> node(typename X::t k, V v, Trie<V> left, Trie<V> right) {
      return Trie(Node{std::move(k), std::move(v),
                       std::make_shared<Trie<V>>(std::move(left)),
                       std::make_shared<Trie<V>>(std::move(right))});
    }

    // MANIPULATORS
    ~Trie() {
      std::vector<std::shared_ptr<Trie<V>>> _stack = {};
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
          _drain(_cur->v_mut());
        }
      }
    }

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
