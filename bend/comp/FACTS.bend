import Base
import ./core.bend as C
import ../keys/FACTS.bend as K

# ---- reference definitions: shared with other units' laws and proofs ----

# The specification plan answers: each component is ready when its turn comes.
def valid_order(o: List<&2, C.Comp>, +avail: List<&2, Nat>) -> Bool:
  match o:
    case Nil{}:
      True{}
    case Con{+c, t}:
      Bool.and(C.ready(c, avail), valid_order(t, List.append(&2, Nat, avail, C.provides(c))))

# avail plus everything the order provides.
def after(o: List<&2, C.Comp>, avail: List<&2, Nat>) -> List<&2, Nat>:
  match o:
    case Nil{}:
      avail
    case Con{c, t}:
      after(t, List.append(&2, Nat, avail, C.provides(c)))

def wf(root: List<&2, Nat>, +o: List<&2, C.Comp>) -> Bool:
  Bool.and(K.distinct(C.ids(o)), K.distinct(List.append(&2, Nat, root, C.keys_of(o))))
