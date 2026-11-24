import Base
import ../comp/core.bend as M

# ---- plan: which components activate, and in what order ----
#
# root is the keys the host provides itself. plan answers an activation order,
# in which each component is ready on root plus what the components before it
# provide, and the components left blocked. A dependency cycle simply never
# becomes ready.
type Plan is Data:
  Plan{order: List<&2, M.Comp>, blocked: List<&2, M.Comp>}

def order_of(p: Plan) -> List<&2, M.Comp>:
  match p:
    case Plan{o, _}:
      o

def blocked_of(p: Plan) -> List<&2, M.Comp>:
  match p:
    case Plan{_, b}:
      b

# The first ready component, and the rest in their order; or all of them.
type Pick is Data:
  Got{c: M.Comp, rest: List<&2, M.Comp>}
  Stuck{all: List<&2, M.Comp>}

def pick.cons(+h: M.Comp, r: Pick) -> Pick:
  match r:
    case Got{c, rest}:
      Got{c, h <> rest}
    case Stuck{all}:
      Stuck{h <> all}

def pick.put(ok: Bool, +h: M.Comp, t: List<&2, M.Comp>, r: Pick) -> Pick:
  match ok:
    case True{}:
      Got{h, t}
    case False{}:
      pick.cons(h, r)

def pick(cs: List<&2, M.Comp>, +avail: List<&2, Nat>) -> Pick:
  match cs:
    case Nil{}:
      Stuck{Nil{}}
    case Con{+h, +t}:
      pick.put(M.ready(h, avail), h, t, pick(t, avail))

def plan.cons(c: M.Comp, p: Plan) -> Plan:
  match p:
    case Plan{o, b}:
      Plan{c <> o, b}

def schedule.next(r: Pick, avail: List<&2, Nat>, k: List<&2, Nat> -> List<&2, M.Comp> -> Plan) -> Plan:
  match r:
    case Stuck{all}:
      Plan{Nil{}, all}
    case Got{+c, rest}:
      plan.cons(c, k(List.append(&2, Nat, avail, M.provides(c)), rest))

# fuel bounds the steps; each step moves one component into the order, so
# fuel >= length(cs) is always enough.
def schedule(fuel: Nat, +avail: List<&2, Nat>, cs: List<&2, M.Comp>) -> Plan:
  match fuel:
    case 0n:
      Plan{Nil{}, cs}
    case 1n+f:
      schedule.next(pick(cs, avail), avail, a => p => schedule(f, a, p))

def plan(root: List<&2, Nat>, +cs: List<&2, M.Comp>) -> Plan:
  schedule(List.length(&2, M.Comp, cs), root, cs)
