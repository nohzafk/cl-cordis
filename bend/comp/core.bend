import Base
import ../keys/core.bend as K

# ---- components ----
#
# A component as the units see it: an id, the keys it injects and the keys it
# provides. plan, check and cascade all answer questions about lists of these.
type Comp is Data:
  Comp{id: Nat, inject: List<&2, Nat>, provide: List<&2, Nat>}

def id_of(c: Comp) -> Nat:
  match c:
    case Comp{id, _, _}:
      id

def provides(c: Comp) -> List<&2, Nat>:
  match c:
    case Comp{_, _, p}:
      p

# c can activate once every key it injects is available.
def ready(c: Comp, +avail: List<&2, Nat>) -> Bool:
  match c:
    case Comp{_, inj, _}:
      K.all_in(inj, avail)

# c must restart when a key it injects is dirty.
def hit(c: Comp, +dirty: List<&2, Nat>) -> Bool:
  match c:
    case Comp{_, inj, _}:
      K.any_in(inj, dirty)

def ids(cs: List<&2, Comp>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      id_of(c) <> ids(t)

# ---- well-formed: what cascade's completeness rests on ----
#
# Ids are distinct, and every key has one source: root, or exactly one
# component. Two providers of one key would leave "which value does the
# consumer see" undecided.
def keys_of(o: List<&2, Comp>) -> List<&2, Nat>:
  match o:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      List.append(&2, Nat, provides(c), keys_of(t))
