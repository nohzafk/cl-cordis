import Base
import ../keys/core.bend as K

# ---- hooks: plugin ownership ----
#
# A hook entry records the plugin that owns it. add refuses an owner already
# present and appends a fresh owner otherwise.
type Entry is Data:
  Entry{plugin: Nat}

def contains(+plugin: Nat, entries: List<&2, Entry>) -> Bool:
  match entries:
    case Nil{}:
      False{}
    case Con{Entry{owner}, t}:
      Bool.or(Nat.is_eq(plugin, owner), contains(plugin, t))

def add.put(hit: Bool, +plugin: Nat, +entries: List<&2, Entry>) -> Maybe<&2, List<&2, Entry>>:
  match hit:
    case True{}:
      None{}
    case False{}:
      Some{List.append(&2, Entry, entries, [Entry{plugin}])}

def add(+plugin: Nat, +entries: List<&2, Entry>) -> Maybe<&2, List<&2, Entry>>:
  add.put(contains(plugin, entries), plugin, entries)

# Drop matching entries; cons each survivor onto the recursively filtered tail.
def remove.put(hit: Bool, owner: Nat, rest: List<&2, Entry>) -> List<&2, Entry>:
  match hit:
    case True{}:
      rest
    case False{}:
      Entry{owner} <> rest

def remove(+plugin: Nat, entries: List<&2, Entry>) -> List<&2, Entry>:
  match entries:
    case Nil{}:
      []
    case Con{Entry{+owner}, t}:
      remove.put(Nat.is_eq(plugin, owner), owner, remove(plugin, t))

# ---- reload: a plugin's place in a chain across a reload ----
#
# A reloaded plugin keeps the place it had. rejoin is the hook's chain once the
# new version stands in for the old: on a hook the new version wraps, the
# plugin's entry stays where it was, and is appended when the old version did
# not wrap that hook; on a hook the new version does not wrap, the entry
# leaves. index is where the plugin's entry stood before the reload, and
# restore puts it back there, so a reload that is refused leaves the chain as
# it found it.
def rejoin.keep(m: Maybe<&2, List<&2, Entry>>, es: List<&2, Entry>) -> List<&2, Entry>:
  match m:
    case None{}:
      es
    case Some{added}:
      added

def rejoin(wraps: Bool, +plugin: Nat, +entries: List<&2, Entry>) -> List<&2, Entry>:
  match wraps:
    case True{}:
      rejoin.keep(add(plugin, entries), entries)
    case False{}:
      remove(plugin, entries)

def index.next(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      Some{1n+n}

def index.put(hit: Bool, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{0n}
    case False{}:
      index.next(rest)

# The position of the plugin's first entry, or None when it owns none.
def index(+plugin: Nat, entries: List<&2, Entry>) -> Maybe<&2, Nat>:
  match entries:
    case Nil{}:
      None{}
    case Con{Entry{owner}, t}:
      index.put(Nat.is_eq(plugin, owner), index(plugin, t))

# The plugin's entry inserted at position n, or appended when n is past the end.
def place(+plugin: Nat, n: Nat, es: List<&2, Entry>) -> List<&2, Entry>:
  match n es:
    case 0n _:
      Entry{plugin} <> es
    case 1n+k Nil{}:
      [Entry{plugin}]
    case 1n+k Con{e, t}:
      e <> place(plugin, k, t)

def restore(at: Maybe<&2, Nat>, +plugin: Nat, +chain: List<&2, Entry>) -> List<&2, Entry>:
  match at:
    case None{}:
      remove(plugin, chain)
    case Some{n}:
      place(plugin, n, remove(plugin, chain))

# ---- chain: which wrapper runs next for one call ----
#
# A call takes a snapshot of the hook's entries when it starts, and that
# snapshot is the call's chain: later registrations and unloads do not touch
# it. Position 0 is the outermost wrapper, so the first registered runs first
# and the host's Default handler is the base of the chain. `add` and `remove`
# pin that registration appends and unload preserves order; `owners`, in LAWS.bend, is the independent spec of which plugins a
# snapshot holds.

# The link that runs: a registered plugin's wrapper, or the host default.
type Link is Data:
  Owner{plugin: Nat}
  Default{}

def to_link(e: Entry) -> Link:
  match e:
    case Entry{owner}:
      Owner{owner}

# The snapshot's link at position n, read through List.get: the entry's owner,
# or Default when n is at or past the end. An empty snapshot has no entry at
# any position, so every position of it is Default.
def step.put(m: Maybe<&2, Entry>) -> Link:
  Maybe.default(&2, Link, Maybe.map(&2, Entry, Link, to_link, m), Default{})

def step(es: List<&2, Entry>, n: Nat) -> Link:
  step.put(List.get(&2, Entry, es, n))

# ---- tokens: the continuation a wrapper is handed ----
#
# A wrapper's `inner` is a token: it names the activation the call belongs to,
# the call itself, and the position of the rest of that call's chain. A call is
# open from the moment it starts until it ends, and a token is usable only
# while its call is open.
#
# The snapshot belongs to the call, not to the caller: opening a call records
# the entries it will run, and no registration or unload afterwards can change
# what that call resolves to. The end of a call's chain is Default, a link like
# any other, so a live token never resolves to a failure.
#
# A token that resolves to nothing says which nothing it is. Unissued (its call
# was never opened) and Ended (its call is over) are different outcomes,
# because a wrapper that arrives too late and one that never had a call are
# different mistakes; a token from another activation is Stale. Nothing in a
# token names another call, so ending one call decides nothing for another.
type Token is Data:
  Token{activation: Nat, call: Nat, position: Nat}

# One call while it is open: its id, and the snapshot it took when it opened.
type Open is Data:
  Open{call: Nat, snapshot: List<&2, Entry>}

# The counter allocates each call id once, and ids are never reused, so the
# counter alone says which ids were ever issued: an id below it is either open
# or ended, an id at or above it is unissued.
type Calls is Data:
  Calls{activation: Nat, next: Nat, open: List<&2, Open>}

# Opening returns the allocated id beside the updated activation state.
type Opened is Data:
  Opened{call: Nat, state: Calls}

# What resolving a token answers. Resolved carries a Link, so failure is never
# encoded as "no link": the base of a chain is Default.
type Outcome is Data:
  Resolved{link: Link}
  Unissued{}
  Ended{}
  Stale{}

def activation_of(t: Token) -> Nat:
  match t:
    case Token{a, _, _}:
      a

def call_of(t: Token) -> Nat:
  match t:
    case Token{_, c, _}:
      c

def position_of(t: Token) -> Nat:
  match t:
    case Token{_, _, p}:
      p

# One activation's calls; its first allocated id is zero.
def begin(+activation: Nat) -> Calls:
  Calls{activation, 0n, []}

def s_activation(s: Calls) -> Nat:
  match s:
    case Calls{a, _, _}:
      a

def next_of(s: Calls) -> Nat:
  match s:
    case Calls{_, next, _}:
      next

def open_of(s: Calls) -> List<&2, Open>:
  match s:
    case Calls{_, _, open}:
      open

def call_at(o: Open) -> Nat:
  match o:
    case Open{c, _}:
      c

def snapshot_of(o: Open) -> List<&2, Entry>:
  match o:
    case Open{_, snapshot}:
      snapshot

# The id of every open call, which is what liveness and ending are read off.
def open_ids(os: List<&2, Open>) -> List<&2, Nat>:
  match os:
    case Nil{}:
      []
    case Con{o, t}:
      call_at(o) <> open_ids(t)

# Allocate the next id and fix this call's snapshot at opening.
def open_call(+snap: List<&2, Entry>, s: Calls) -> Opened:
  match s:
    case Calls{a, +next, open}:
      Opened{next, Calls{a, 1n+next, Open{next, snap} <> open}}

def drop_open.put(hit: Bool, o: Open, kept: List<&2, Open>) -> List<&2, Open>:
  match hit:
    case True{}:
      kept
    case False{}:
      o <> kept

def drop_open(+call: Nat, os: List<&2, Open>) -> List<&2, Open>:
  match os:
    case Nil{}:
      []
    case Con{+o, t}:
      drop_open.put(Nat.is_eq(call, call_at(o)), o, drop_open(call, t))

def end_call.take(+call: Nat, s: Calls) -> Calls:
  match s:
    case Calls{a, next, open}:
      Calls{a, next, drop_open(call, open)}

def end_call.put(is_open: Bool, +call: Nat, s: Calls) -> Calls:
  match is_open:
    case True{}:
      end_call.take(call, s)
    case False{}:
      s

# Ending a call: it stops being open, and being below the counter and not open
# is what makes it ended, so a token that arrives afterwards is answered Ended
# and never Unissued. Ending a call that was never opened changes nothing, so
# ending one twice is ending it once, and an unissued token still reads as
# unissued.
def end_call(+call: Nat, +s: Calls) -> Calls:
  end_call.put(K.mem(call, open_ids(open_of(s))), call, s)

def gone.put(has_ended: Bool) -> Outcome:
  match has_ended:
    case True{}:
      Ended{}
    case False{}:
      Unissued{}

# A token that is not live: its call was issued (its id is below the counter)
# and is not open, so it ended; or its id is at or above the counter, so it was
# never opened.
def gone(+t: Token, +s: Calls) -> Outcome:
  gone.put(Nat.is_lt(call_of(t), next_of(s)))

def resume.at(hit: Bool, snap: List<&2, Entry>, +t: Token, r: Outcome) -> Outcome:
  match hit:
    case True{}:
      Resolved{step(snap, position_of(t))}
    case False{}:
      r

# A token whose activation matches: the link its own call's snapshot names at
# its position, or the reason there is none.
def resume(+call: Nat, +t: Token, +os: List<&2, Open>, r: Outcome) -> Outcome:
  match os:
    case Nil{}:
      r
    case Con{+o, rest}:
      resume.at(Nat.is_eq(call, call_at(o)), snapshot_of(o), t, resume(call, t, rest, r))

def resolve.call(+t: Token, +s: Calls) -> Outcome:
  resume(call_of(t), t, open_of(s), gone(t, s))

def resolve.activation(same: Bool, +t: Token, +s: Calls) -> Outcome:
  match same:
    case True{}:
      resolve.call(t, s)
    case False{}:
      Stale{}

# What a token resolves to: the link its continuation runs, read from the
# snapshot its own call took, or the reason it resolves to nothing. It takes no
# entry list, so nothing outside the call's own snapshot can change the answer.
def resolve(+t: Token, +s: Calls) -> Outcome:
  resolve.activation(Nat.is_eq(activation_of(t), s_activation(s)), t, s)

# What issuing a continuation answers: the token for the rest of the chain
# beside the updated activation state.
type Issued is Data:
  Issued{token: Token, state: Calls}

def token_of(r: Issued) -> Token:
  match r:
    case Issued{token, _}:
      token

def state_of(r: Issued) -> Calls:
  match r:
    case Issued{_, state}:
      state

def issue.with(+position: Nat, +activation: Nat, r: Opened) -> Issued:
  match r:
    case Opened{call, state}:
      Issued{Token{activation, call, 1n+position}, state}

# The `inner` handed to the wrapper at `position`: it opens the call's own
# snapshot and names the next link, position + 1, of that chain.
def issue(+position: Nat, +snap: List<&2, Entry>, +s: Calls) -> Issued:
  issue.with(position, s_activation(s), open_call(snap, s))

def finish.put(same: Bool, +t: Token, +s: Calls) -> Calls:
  match same:
    case True{}:
      end_call(call_of(t), s)
    case False{}:
      s

# Ending a call by its token: only a token of this activation names one of this
# activation's calls; a token of an earlier activation ends nothing.
def finish(+t: Token, +s: Calls) -> Calls:
  finish.put(Nat.is_eq(activation_of(t), s_activation(s)), t, s)
