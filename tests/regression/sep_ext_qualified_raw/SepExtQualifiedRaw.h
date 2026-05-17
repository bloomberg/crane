#ifndef INCLUDED_SEPEXTQUALIFIEDRAW
#define INCLUDED_SEPEXTQUALIFIEDRAW

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

namespace SepExtQualifiedRaw {

template <typename M>
concept OrderedType = requires { typename M::t; };

template <OrderedType X> struct Make {
  template <typename t_A> struct Fmap {
    // TYPES
    struct Empty {};

    struct Node {
      typename X::t d_a0;
      t_A d_a1;
      std::unique_ptr<Fmap<t_A>> d_a2;
    };

    using variant_t = std::variant<Empty, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Fmap() {}

    explicit Fmap(Empty _v) : d_v_(_v) {}

    explicit Fmap(Node _v) : d_v_(std::move(_v)) {}

    Fmap(const Fmap<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Fmap(Fmap<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    Fmap<t_A> &operator=(const Fmap<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Fmap<t_A> &operator=(Fmap<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    Fmap<t_A> clone() const {
      Fmap<t_A> _out{};

      struct _CloneFrame {
        const Fmap<t_A> *_src;
        Fmap<t_A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const Fmap<t_A> *_src = _frame._src;
        Fmap<t_A> *_dst = _frame._dst;
        if (std::holds_alternative<Empty>(_src->v())) {
          _dst->d_v_ = Empty{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node{_alt.d_a0, _alt.d_a1,
                   _alt.d_a2 ? std::make_unique<Fmap<t_A>>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit Fmap(const Fmap<_U> &_other) {
      if (std::holds_alternative<typename Fmap<_U>::Empty>(_other.v())) {
        this->d_v_ = Empty{};
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename Fmap<_U>::Node>(_other.v());
        this->d_v_ = Node{d_a0, t_A(d_a1),
                          d_a2 ? std::make_unique<Fmap<t_A>>(*d_a2) : nullptr};
      }
    }

    static Fmap<t_A> empty() { return Fmap(Empty{}); }

    static Fmap<t_A> node(typename X::t a0, t_A a1, Fmap<t_A> a2) {
      return Fmap(Node{std::move(a0), std::move(a1),
                       std::make_unique<Fmap<t_A>>(std::move(a2))});
    }

    // MANIPULATORS
    ~Fmap() {
      std::vector<std::unique_ptr<Fmap<t_A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](Fmap<t_A> &_node) {
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
    requires std::is_invocable_r_v<T2, F1 &, typename X::t &, T1 &, Fmap<T1> &,
                                   T2 &>
  static T2 fmap_rect(T2 f, F1 &&f0, const Fmap<T1> &f1) {
    if (std::holds_alternative<typename Fmap<T1>::Empty>(f1.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Fmap<T1>::Node>(f1.v());
      return f0(d_a0, d_a1, *d_a2, fmap_rect<T1, T2>(f, f0, *d_a2));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, typename X::t &, T1 &, Fmap<T1> &,
                                   T2 &>
  static T2 fmap_rec(T2 f, F1 &&f0, const Fmap<T1> &f1) {
    if (std::holds_alternative<typename Fmap<T1>::Empty>(f1.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Fmap<T1>::Node>(f1.v());
      return f0(d_a0, d_a1, *d_a2, fmap_rec<T1, T2>(f, f0, *d_a2));
    }
  }

  template <typename T1> static bool is_empty(const Fmap<T1> &m) {
    if (std::holds_alternative<typename Fmap<T1>::Empty>(m.v())) {
      return true;
    } else {
      return false;
    }
  }
};

} // namespace SepExtQualifiedRaw

#endif // INCLUDED_SEPEXTQUALIFIEDRAW
