#ifndef INCLUDED_SEPEXTSELFREFINDUCTIVE
#define INCLUDED_SEPEXTSELFREFINDUCTIVE

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
      std::unique_ptr<Trie<V>> left;
      std::unique_ptr<Trie<V>> right;
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

    Trie(const Trie<V> &_other) : v_(std::move(_other.clone().v_)) {}

    Trie(Trie<V> &&_other) : v_(std::move(_other.v_)) {}

    Trie<V> &operator=(const Trie<V> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    Trie<V> &operator=(Trie<V> &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    Trie<V> clone() const {
      Trie<V> _out{};

      struct _CloneFrame {
        const Trie<V> *_src;
        Trie<V> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const Trie<V> *_src = _frame._src;
        Trie<V> *_dst = _frame._dst;
        if (std::holds_alternative<Empty>(_src->v())) {
          _dst->v_ = Empty{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ = Node{_alt.k, _alt.v,
                          _alt.left ? std::make_unique<Trie<V>>() : nullptr,
                          _alt.right ? std::make_unique<Trie<V>>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
          if (_alt.left) {
            _stack.push_back({_alt.left.get(), _dst_alt.left.get()});
          }
          if (_alt.right) {
            _stack.push_back({_alt.right.get(), _dst_alt.right.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit Trie(const Trie<_U> &_other) {
      if (std::holds_alternative<typename Trie<_U>::Empty>(_other.v())) {
        this->v_ = Empty{};
      } else {
        const auto &[k, v, left, right] =
            std::get<typename Trie<_U>::Node>(_other.v());
        this->v_ =
            Node{k, V(v), left ? std::make_unique<Trie<V>>(*left) : nullptr,
                 right ? std::make_unique<Trie<V>>(*right) : nullptr};
      }
    }

    static Trie<V> empty() { return Trie(Empty{}); }

    static Trie<V> node(typename X::t k, V v, Trie<V> left, Trie<V> right) {
      return Trie(Node{std::move(k), std::move(v),
                       std::make_unique<Trie<V>>(std::move(left)),
                       std::make_unique<Trie<V>>(std::move(right))});
    }

    // MANIPULATORS
    ~Trie() {
      std::vector<std::unique_ptr<Trie<V>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](Trie<V> &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.left) {
            _stack.push_back(std::move(_alt.left));
          }
          if (_alt.right) {
            _stack.push_back(std::move(_alt.right));
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
