#ifndef INCLUDED_MUTUAL_MOD
#define INCLUDED_MUTUAL_MOD

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct EvenOdd {
  struct even_list;
  struct odd_list;

  struct even_list {
    // TYPES
    struct ENil {};

    struct ECons {
      unsigned int d_a0;
      std::unique_ptr<odd_list> d_a1;
    };

    using variant_t = std::variant<ENil, ECons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    even_list() {}

    explicit even_list(ENil _v) : d_v_(_v) {}

    explicit even_list(ECons _v) : d_v_(std::move(_v)) {}

    even_list(const even_list &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    even_list(even_list &&_other) : d_v_(std::move(_other.d_v_)) {}

    even_list &operator=(const even_list &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    even_list &operator=(even_list &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    even_list clone() const {
      even_list _out{};

      struct _CloneFrame {
        const even_list *_src;
        even_list *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const even_list *_src = _frame._src;
        even_list *_dst = _frame._dst;
        if (std::holds_alternative<ENil>(_src->v())) {
          _dst->d_v_ = ENil{};
        } else {
          const auto &_alt = std::get<ECons>(_src->v());
          _dst->d_v_ =
              ECons{_alt.d_a0, _alt.d_a1 ? std::make_unique<EvenOdd::odd_list>()
                                         : nullptr};
          auto &_dst_alt = std::get<ECons>(_dst->d_v_);
          if (_alt.d_a1) {
            if (std::holds_alternative<typename EvenOdd::odd_list::OCons>(
                    _alt.d_a1->v())) {
              const auto &_psrc =
                  std::get<typename EvenOdd::odd_list::OCons>(_alt.d_a1->v());
              auto &_pdst = std::get<typename EvenOdd::odd_list::OCons>(
                  _dst_alt.d_a1->v_mut());
              if (_psrc.d_a1) {
                _pdst.d_a1 = std::make_unique<EvenOdd::even_list>();
                _stack.push_back({_psrc.d_a1.get(), _pdst.d_a1.get()});
              }
            }
          }
        }
      }
      return _out;
    }

    // CREATORS
    static even_list enil() { return even_list(ENil{}); }

    static even_list econs(unsigned int a0, odd_list a1) {
      return even_list(
          ECons{std::move(a0), std::make_unique<odd_list>(std::move(a1))});
    }

    // MANIPULATORS
    ~even_list() {
      std::vector<std::unique_ptr<even_list>> _stack{};
      auto _drain = [&](even_list &_node) {
        if (std::holds_alternative<ECons>(_node.d_v_)) {
          auto &_alt = std::get<ECons>(_node.d_v_);
          if (_alt.d_a1) {
            if (std::holds_alternative<typename EvenOdd::odd_list::OCons>(
                    _alt.d_a1->v())) {
              auto &_palt = std::get<typename EvenOdd::odd_list::OCons>(
                  _alt.d_a1->v_mut());
              if (_palt.d_a1) {
                _stack.push_back(std::move(_palt.d_a1));
              }
            }
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

  struct odd_list {
    // TYPES
    struct OCons {
      unsigned int d_a0;
      std::unique_ptr<even_list> d_a1;
    };

    using variant_t = std::variant<OCons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    odd_list() {}

    explicit odd_list(OCons _v) : d_v_(std::move(_v)) {}

    odd_list(const odd_list &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    odd_list(odd_list &&_other) : d_v_(std::move(_other.d_v_)) {}

    odd_list &operator=(const odd_list &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    odd_list &operator=(odd_list &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    odd_list clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<OCons>(_sv.v());
      return odd_list(
          OCons{d_a0, d_a1 ? std::make_unique<EvenOdd::even_list>(d_a1->clone())
                           : nullptr});
    }

    // CREATORS
    static odd_list ocons(unsigned int a0, even_list a1) {
      return odd_list(
          OCons{std::move(a0), std::make_unique<even_list>(std::move(a1))});
    }

    // MANIPULATORS
    ~odd_list() {
      std::vector<std::unique_ptr<odd_list>> _stack{};
      auto _drain = [&](odd_list &_node) {
        if (std::holds_alternative<OCons>(_node.d_v_)) {
          auto &_alt = std::get<OCons>(_node.d_v_);
          if (_alt.d_a1) {
            if (std::holds_alternative<typename EvenOdd::even_list::ECons>(
                    _alt.d_a1->v())) {
              auto &_palt = std::get<typename EvenOdd::even_list::ECons>(
                  _alt.d_a1->v_mut());
              if (_palt.d_a1) {
                _stack.push_back(std::move(_palt.d_a1));
              }
            }
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

  static unsigned int even_length(const even_list &e);
  static unsigned int odd_length(const odd_list &o);
  static inline const even_list two =
      even_list::econs(2u, odd_list::ocons(1u, even_list::enil()));
  static inline const odd_list three = odd_list::ocons(
      3u, even_list::econs(2u, odd_list::ocons(1u, even_list::enil())));
};

const unsigned int test_even_len = EvenOdd::even_length(EvenOdd::two);
const unsigned int test_odd_len = EvenOdd::odd_length(EvenOdd::three);

#endif // INCLUDED_MUTUAL_MOD
