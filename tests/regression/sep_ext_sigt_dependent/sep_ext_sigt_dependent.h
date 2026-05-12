#ifndef INCLUDED_SEP_EXT_SIGT_DEPENDENT
#define INCLUDED_SEP_EXT_SIGT_DEPENDENT

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename t_A, typename t_P> struct SigT {
  // TYPES
  struct ExistT {
    t_A d_x;
    t_P d_a1;
  };

  using variant_t = std::variant<ExistT>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  SigT() {}

  explicit SigT(ExistT _v) : d_v_(std::move(_v)) {}

  SigT(const SigT<t_A, t_P> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  SigT(SigT<t_A, t_P> &&_other) : d_v_(std::move(_other.d_v_)) {}

  SigT<t_A, t_P> &operator=(const SigT<t_A, t_P> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  SigT<t_A, t_P> &operator=(SigT<t_A, t_P> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  SigT<t_A, t_P> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x, d_a1] = std::get<ExistT>(_sv.v());
    return SigT<t_A, t_P>(ExistT(d_x, d_a1));
  }

  // CREATORS
  template <typename _U0, typename _U1>
  explicit SigT(const SigT<_U0, _U1> &_other) {
    const auto &[d_x, d_a1] =
        std::get<typename SigT<_U0, _U1>::ExistT>(_other.v());
    this->d_v_ = ExistT(t_A(d_x), t_P(d_a1));
  }

  static SigT<t_A, t_P> existt(t_A x, t_P a1) {
    return SigT(ExistT(std::move(x), std::move(a1)));
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }

  t_A projT1() const {
    auto &&_sv = *(this);
    const auto &[d_x, d_a1] =
        std::get<typename SigT<t_A, t_P>::ExistT>(_sv.v());
    return d_x;
  }
};
enum class Tag { e_TAGA, e_TAGB, e_TAGC };
using tag_type = std::any;

struct Packer {
  static inline const SigT<Tag, tag_type> pack_a =
      SigT<Tag, std::any>::existt(Tag::e_TAGA, std::monostate{});
  static SigT<Tag, tag_type> pack_b(const unsigned int n);
  static SigT<Tag, tag_type> pack_c(const bool b);
  static Tag get_tag(const SigT<Tag, tag_type> &_x0);
};

#endif // INCLUDED_SEP_EXT_SIGT_DEPENDENT
