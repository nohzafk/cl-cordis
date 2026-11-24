import Base
import ./core.bend as C
import ../comp/core.bend as M
import ../comp/FACTS.bend as MF
import ../keys/FACTS.bend as K

# Every law here is approved, and proved in PROOF.bend.
#
# check: the validating layer
#   check_exact, check_accurate

# ---- reference definitions: what the laws are stated with ----

# The defect an error names is there: the id, or the key, occurs twice.
def real(e: C.Err, root: List<&2, Nat>, +cs: List<&2, M.Comp>) -> Bool:
  match e:
    case C.DupId{+i}:
      Nat.is_lt(1n, K.count(i, M.ids(cs)))
    case C.DupKey{+k}:
      Nat.is_lt(1n, K.count(k, List.append(&2, Nat, root, M.keys_of(cs))))

# Guarantees: check reports no error exactly when the components are well-formed for the
#   root keys (no premises).
# Why it matters: A duplicate id or key could pass into the runtime, or a clean input could
#   be refused.
law check_exact:
  for +root: List<&2, Nat>
  for +cs: List<&2, M.Comp>
  {Maybe.is_none(&2, C.Err, C.check(root, cs)) == MF.wf(root, cs) : Bool}

# Guarantees: When check reports an error, the id or key it names really occurs more than
#   once (premise: check returned that error).
# Why it matters: The user would be told to fix a duplicate that is not there, and look for
#   it in vain.
law check_accurate:
  for +root: List<&2, Nat>
  for +cs: List<&2, M.Comp>
  for +e: C.Err
  for h: {C.check(root, cs) == Some{e} : Maybe<&2, C.Err>}
  {real(e, root, cs) == True{} : Bool}

