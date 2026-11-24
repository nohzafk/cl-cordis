import Base

# The decisions of the Cordis paradigm live in the units beside this one, one
# pure concern each, with no effects. The host (TypeScript, on Effect) owns
# every effect, closure and Worker; it asks the units and does what they answer.
#
# Ids and keys are Nat: the host interns its strings and maps them back. This
# unit is what every other unit stands on: lists of Nats read as sets.

# ---- keys ----
def mem(+k: Nat, ks: List<&2, Nat>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Nat.is_eq(k, h), mem(k, t))

def all_in(ks: List<&2, Nat>, +avail: List<&2, Nat>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(mem(h, avail), all_in(t, avail))

def any_in(ks: List<&2, Nat>, +dirty: List<&2, Nat>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(mem(h, dirty), any_in(t, dirty))

def first_dup.put(rep: Bool, +h: Nat, r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match rep:
    case True{}:
      Some{h}
    case False{}:
      r

def first_dup(ks: List<&2, Nat>) -> Maybe<&2, Nat>:
  match ks:
    case Nil{}:
      None{}
    case Con{+h, +t}:
      first_dup.put(mem(h, t), h, first_dup(t))

# ---- missing: the first name not in a set ----
#
# One lookup, two questions: which declared key does the host's catalog not
# know, and which provided key has an activation not set yet.
def missing.put(have: Bool, +h: Nat, r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match have:
    case True{}:
      r
    case False{}:
      Some{h}

def missing(ks: List<&2, Nat>, +have: List<&2, Nat>) -> Maybe<&2, Nat>:
  match ks:
    case Nil{}:
      None{}
    case Con{+h, t}:
      missing.put(mem(h, have), h, missing(t, have))

# ---- add and remove ----

# ks with k put in front unless it is already there.
def add.put(have: Bool, k: Nat, ks: List<&2, Nat>) -> List<&2, Nat>:
  match have:
    case True{}:
      ks
    case False{}:
      k <> ks

def add(+k: Nat, +ks: List<&2, Nat>) -> List<&2, Nat>:
  add.put(mem(k, ks), k, ks)

# ks without k.
def remove.put(same: Bool, +h: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match same:
    case True{}:
      r
    case False{}:
      h <> r

def remove(+k: Nat, ks: List<&2, Nat>) -> List<&2, Nat>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      remove.put(Nat.is_eq(k, h), h, remove(k, t))
