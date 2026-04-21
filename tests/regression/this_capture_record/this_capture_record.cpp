#include <this_capture_record.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Methodified on tree. The extra flag argument forces Crane to
/// treat this as a multi-argument function (preventing eta-collapse).
/// Returns a record whose fields are closures that capture this
/// via =, this.
std::shared_ptr<ThisCaptureRecord::callback_rec>
ThisCaptureRecord::tree_callbacks(std::shared_ptr<ThisCaptureRecord::tree> t,
                                  const unsigned int flag) {
  if (flag <= 0) {
    return std::make_shared<ThisCaptureRecord::callback_rec>(callback_rec{
        [=](const unsigned int x) mutable { return (x + t->tree_sum()); },
        [=](const unsigned int x) mutable { return (x * t->tree_sum()); }});
  } else {
    unsigned int _x = flag - 1;
    return std::make_shared<ThisCaptureRecord::callback_rec>(callback_rec{
        [=](const unsigned int x) mutable { return (t->tree_sum() + x); },
        [=](const unsigned int) mutable { return t->tree_sum(); }});
  }
}

/// Dummy use of tag to keep it around for extraction.
std::shared_ptr<ThisCaptureRecord::tag>
ThisCaptureRecord::mk_tag(const unsigned int n) {
  return tag::mktag(n);
}
