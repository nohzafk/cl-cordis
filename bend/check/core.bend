import Base
import ../keys/core.bend as K
import ../comp/core.bend as M

# ---- check: the validating layer ----
#
# check answers the first defect, or None when the components are well-formed.
# The first duplicate id wins over any duplicate key; within each, the first
# in list order. One error is enough to fix the input and try again.
type Err is Data:
  DupId{id: Nat}
  DupKey{key: Nat}

def check.keys(m: Maybe<&2, Nat>) -> Maybe<&2, Err>:
  match m:
    case None{}:
      None{}
    case Some{k}:
      Some{DupKey{k}}

def check.put(m: Maybe<&2, Nat>, keys: Maybe<&2, Err>) -> Maybe<&2, Err>:
  match m:
    case None{}:
      keys
    case Some{i}:
      Some{DupId{i}}

def check(root: List<&2, Nat>, +cs: List<&2, M.Comp>) -> Maybe<&2, Err>:
  check.put(K.first_dup(M.ids(cs)), check.keys(K.first_dup(List.append(&2, Nat, root, M.keys_of(cs)))))
