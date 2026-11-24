import Base
import ../comp/core.bend as M

# ---- cascade: which active components restart when keys change ----
#
# Walks an activation order once. A component that injects a dirty key
# restarts, and everything it provides becomes dirty for those after it.
# Answers the restarting components in activation order: stop them in the
# reverse of it, start them in it.
def cascade.put(hit: Bool, +c: M.Comp, dirty: List<&2, Nat>, k: List<&2, Nat> -> List<&2, M.Comp>) -> List<&2, M.Comp>:
  match hit:
    case True{}:
      c <> k(List.append(&2, Nat, dirty, M.provides(c)))
    case False{}:
      k(dirty)

def cascade(o: List<&2, M.Comp>, +dirty: List<&2, Nat>) -> List<&2, M.Comp>:
  match o:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      cascade.put(M.hit(c, dirty), c, dirty, d => cascade(t, d))
