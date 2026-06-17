#ifndef INCLUDED_PARSERANYCAST
#define INCLUDED_PARSERANYCAST

#include <any>
#include <utility>
#include <variant>

#include "Ascii.h"
#include "Datatypes.h"
#include "List.h"
#include "ListDef.h"
#include "Specif.h"
#include "String_.h"

namespace ParserAnyCast {

struct ParserAnyCast {
  enum class Tag { A, B };
  using sem_ty = std::any;
  using entry = Specif::SigT<Tag, sem_ty>;

  static const entry &entry_a() {
    static const entry v =
        Specif::template SigT<Tag, std::any>::existt(Tag::A, UINT64_C(42));
    return v;
  }

  static const entry &entry_b() {
    static const entry v = Specif::template SigT<Tag, std::any>::existt(
        Tag::B,
        String::String::string0(
            Ascii::Ascii::ascii0(false, false, false, true, false, true, true,
                                 false),
            String::String::string0(
                Ascii::Ascii::ascii0(true, false, true, false, false, true,
                                     true, false),
                String::String::string0(
                    Ascii::Ascii::ascii0(false, false, true, true, false, true,
                                         true, false),
                    String::String::string0(
                        Ascii::Ascii::ascii0(false, false, true, true, false,
                                             true, true, false),
                        String::String::string0(
                            Ascii::Ascii::ascii0(true, true, true, true, false,
                                                 true, true, false),
                            String::String::emptystring()))))));
    return v;
  }

  static Tag get_tag(entry _x0);
  static Datatypes::List<Tag>
  process_entries(const Datatypes::List<Specif::SigT<Tag, std::any>> &es);

  static const Datatypes::List<entry> &test_entries() {
    static const Datatypes::List<entry> v =
        Datatypes::template List<Specif::SigT<Tag, std::any>>::cons(
            entry_a(),
            Datatypes::template List<Specif::SigT<Tag, std::any>>::cons(
                entry_b(),
                Datatypes::template List<Specif::SigT<Tag, std::any>>::nil()));
    return v;
  }

  static const Datatypes::List<Tag> &test_result() {
    static const Datatypes::List<Tag> v = process_entries(test_entries());
    return v;
  }

  static uint64_t get_a_value(const Specif::SigT<Tag, std::any> &e);
  static uint64_t
  sum_a_entries(const Datatypes::List<Specif::SigT<Tag, std::any>> &es);

  static const uint64_t &test_sum() {
    static const uint64_t v = sum_a_entries(test_entries());
    return v;
  }
  enum class Label { NUML, STRL, UNITL };
  using label_sem = std::any;

  static const Label &def_label() {
    static const Label v = Label::UNITL;
    return v;
  }

  static const label_sem &def_literal() {
    static const label_sem v = std::any_cast<label_sem>(std::monostate{});
    return v;
  }

  using labeled_entry = Specif::SigT<Label, label_sem>;

  static const labeled_entry &make_default_entry() {
    static const labeled_entry v =
        Specif::template SigT<Label, std::any>::existt(def_label(),
                                                       def_literal());
    return v;
  }

  static Label get_entry_label(labeled_entry _x0);

  static const Label &test_default_label() {
    static const Label v = get_entry_label(make_default_entry());
    return v;
  }
};

} // namespace ParserAnyCast

#endif // INCLUDED_PARSERANYCAST
