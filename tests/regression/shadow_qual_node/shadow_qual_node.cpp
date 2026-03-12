#include <shadow_qual_node.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

ShadowQualNode::Node::shadow
ShadowQualNode::id(const ShadowQualNode::Node::shadow x) {
  return x;
}
