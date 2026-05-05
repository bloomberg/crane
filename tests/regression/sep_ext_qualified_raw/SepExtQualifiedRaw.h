#ifndef INCLUDED_SEPEXTQUALIFIEDRAW
#define INCLUDED_SEPEXTQUALIFIEDRAW

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

namespace SepExtQualifiedRaw {

template <typename M>
concept OrderedType = requires { typename M::t; };

template <OrderedType X> struct Make {
  template <typename t_A> struct fmap {
    // TYPES
    struct Empty {};

    struct Node {
      typename X::t d_a0;
      t_A d_a1;
      std::unique_ptr<fmap<t_A>> d_a2;
    };

    using variant_t = std::variant<Empty, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    fmap() {}

    explicit fmap(Empty _v) : d_v_(_v) {}

    explicit fmap(Node _v) : d_v_(std::move(_v)) {}

    fmap(const fmap<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    fmap(fmap<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    fmap<t_A> &operator=(const fmap<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    fmap<t_A> &operator=(fmap<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    fmap<t_A> clone() const {
      fmap<t_A> _out{};

      struct _CloneFrame {
        const fmap<t_A> *_src;
        fmap<t_A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const fmap<t_A> *_src = _frame._src;
        fmap<t_A> *_dst = _frame._dst;
        if (std::holds_alternative<Empty>(_src->v())) {
          _dst->d_v_ = Empty{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node{_alt.d_a0, _alt.d_a1,
                   _alt.d_a2 ? std::make_unique<fmap<t_A>>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit fmap(const fmap<_U> &_other) {
      if (std::holds_alternative<typename fmap<_U>::Empty>(_other.v())) {
        this->d_v_ = Empty{};
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename fmap<_U>::Node>(_other.v());
        this->d_v_ =
            Node{d_a0, t_A(d_a1),
                 d_a2 ? std::make_unique<Make::fmap<t_A>>(*d_a2) : nullptr};
      }
    }

    static fmap<t_A> empty() { return fmap(Empty{}); }

    static fmap<t_A> node(typename X::t a0, t_A a1, fmap<t_A> a2) {
      return fmap(Node{std::move(a0), std::move(a1),
                       std::make_unique<fmap<t_A>>(std::move(a2))});
    }

    // MANIPULATORS
    ~fmap() {
      std::vector<std::unique_ptr<fmap<t_A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](fmap<t_A> &_node) {
        if (std::holds_alternative<Node>(_node.d_v_)) {
          auto &_alt = std::get<Node>(_node.d_v_);
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
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
    requires std::is_invocable_r_v<T2, F1 &, typename X::t &, T1 &, fmap<T1> &,
                                   T2 &>
  static T2 fmap_rect(const T2 f, F1 &&f0, const fmap<T1> &f1) {
    if (std::holds_alternative<typename fmap<T1>::Empty>(f1.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename fmap<T1>::Node>(f1.v());
      return f0(d_a0, d_a1, *(d_a2), fmap_rect<T1, T2>(f, f0, *(d_a2)));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, typename X::t &, T1 &, fmap<T1> &,
                                   T2 &>
  static T2 fmap_rec(const T2 f, F1 &&f0, const fmap<T1> &f1) {
    if (std::holds_alternative<typename fmap<T1>::Empty>(f1.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename fmap<T1>::Node>(f1.v());
      return f0(d_a0, d_a1, *(d_a2), fmap_rec<T1, T2>(f, f0, *(d_a2)));
    }
  }

  template <typename T1> static bool is_empty(const fmap<T1> &m) {
    if (std::holds_alternative<typename fmap<T1>::Empty>(m.v())) {
      return true;
    } else {
      return false;
    }
  }
};

} // namespace SepExtQualifiedRaw

#endif // INCLUDED_SEPEXTQUALIFIEDRAW
