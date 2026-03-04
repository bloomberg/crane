#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <shadow_qual_node.h>
#include <stdexcept>
#include <string>
#include <variant>

Node::shadow ShadowQualNode::id(const Node::shadow x) { return x; }
