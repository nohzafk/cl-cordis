import Base
import ./core.bend as C

# Every law here is approved, and proved in PROOF.bend.
#
# missing: the first name not in a set
#   missing_exact, missing_accurate

# Guarantees: missing finds nothing exactly when every asked name is in the set (no
#   premises).
# Why it matters: An unknown key could be let through, or a known key refused.
law missing_exact:
  for +ks: List<&2, Nat>
  for +have: List<&2, Nat>
  {Maybe.is_none(&2, Nat, C.missing(ks, have)) == C.all_in(ks, have) : Bool}

# Guarantees: When missing reports a name, that name is one of the names asked about and it
#   is absent from the set (premise: missing returned that name).
# Why it matters: The error would name a key that is present or was never asked about, and
#   the user would fix the wrong key.
law missing_accurate:
  for +ks: List<&2, Nat>
  for +have: List<&2, Nat>
  for +k: Nat
  for h: {C.missing(ks, have) == Some{k} : Maybe<&2, Nat>}
  {Bool.and(C.mem(k, ks), Bool.not(C.mem(k, have))) == True{} : Bool}
