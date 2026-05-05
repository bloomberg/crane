#ifndef INCLUDED_SEPEXTSELFREFINDUCTIVE
#define INCLUDED_SEPEXTSELFREFINDUCTIVE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

namespace SepExtSelfRefInductive {

template <typename M>
concept S = requires { typename M::t; };

template <S X> struct HashTrie {
  template <typename t_V> struct Trie {
    // TYPES
    struct Empty {};

    struct Node {
      typename X::t d_k;
      t_V d_v;
      std::unique_ptr<Trie<t_V>> d_left;
      std::unique_ptr<Trie<t_V>> d_right;
    };

    using variant_t = std::variant<Empty, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Trie() {}

    explicit Trie(Empty _v) : d_v_(_v) {}

    explicit Trie(Node _v) : d_v_(std::move(_v)) {}

    Trie(const Trie<t_V> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Trie(Trie<t_V> &&_other) : d_v_(std::move(_other.d_v_)) {}

    Trie<t_V> &operator=(const Trie<t_V> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Trie<t_V> &operator=(Trie<t_V> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    Trie<t_V> clone() const {
      Trie<t_V> _out{};

      struct _CloneFrame {
        const Trie<t_V> *_src;
        Trie<t_V> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const Trie<t_V> *_src = _frame._src;
        Trie<t_V> *_dst = _frame._dst;
        if (std::holds_alternative<Empty>(_src->v())) {
          _dst->d_v_ = Empty{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node{_alt.d_k, _alt.d_v,
                   _alt.d_left ? std::make_unique<Trie<t_V>>() : nullptr,
                   _alt.d_right ? std::make_unique<Trie<t_V>>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_left) {
            _stack.push_back({_alt.d_left.get(), _dst_alt.d_left.get()});
          }
          if (_alt.d_right) {
            _stack.push_back({_alt.d_right.get(), _dst_alt.d_right.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit Trie(const Trie<_U> &_other) {
      if (std::holds_alternative<typename Trie<_U>::Empty>(_other.v())) {
        this->d_v_ = Empty{};
      } else {
        const auto &[d_k, d_v, d_left, d_right] =
            std::get<typename Trie<_U>::Node>(_other.v());
        this->d_v_ = Node{
            d_k, t_V(d_v),
            d_left ? std::make_unique<HashTrie::Trie<t_V>>(*d_left) : nullptr,
            d_right ? std::make_unique<HashTrie::Trie<t_V>>(*d_right)
                    : nullptr};
      }
    }

    static Trie<t_V> empty() { return Trie(Empty{}); }

    static Trie<t_V> node(typename X::t k, t_V v, Trie<t_V> left,
                          Trie<t_V> right) {
      return Trie(Node{std::move(k), std::move(v),
                       std::make_unique<Trie<t_V>>(std::move(left)),
                       std::make_unique<Trie<t_V>>(std::move(right))});
    }

    // MANIPULATORS
    ~Trie() {
      std::vector<std::unique_ptr<Trie<t_V>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](Trie<t_V> &_node) {
        if (std::holds_alternative<Node>(_node.d_v_)) {
          auto &_alt = std::get<Node>(_node.d_v_);
          if (_alt.d_left) {
            _stack.push_back(std::move(_alt.d_left));
          }
          if (_alt.d_right) {
            _stack.push_back(std::move(_alt.d_right));
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
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, typename X::t &, T1 &, Trie<T1> &,
                                   T2 &, Trie<T1> &, T2 &>
  static T2 Trie_rect(const T2 f, F1 &&f0, const Trie<T1> &t0) {
    if (std::holds_alternative<typename Trie<T1>::Empty>(t0.v())) {
      return f;
    } else {
      const auto &[d_k, d_v, d_left, d_right] =
          std::get<typename Trie<T1>::Node>(t0.v());
      return f0(d_k, d_v, *(d_left), Trie_rect<T1, T2>(f, f0, *(d_left)),
                *(d_right), Trie_rect<T1, T2>(f, f0, *(d_right)));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, typename X::t &, T1 &, Trie<T1> &,
                                   T2 &, Trie<T1> &, T2 &>
  static T2 Trie_rec(const T2 f, F1 &&f0, const Trie<T1> &t0) {
    if (std::holds_alternative<typename Trie<T1>::Empty>(t0.v())) {
      return f;
    } else {
      const auto &[d_k, d_v, d_left, d_right] =
          std::get<typename Trie<T1>::Node>(t0.v());
      return f0(d_k, d_v, *(d_left), Trie_rec<T1, T2>(f, f0, *(d_left)),
                *(d_right), Trie_rec<T1, T2>(f, f0, *(d_right)));
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
