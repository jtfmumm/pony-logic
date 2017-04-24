use "collections"
use pers = "collections/persistent"

type Value is String
type Term is (Value | Var | Pair)

class val Var is Equatable[Var]
  let id: USize
  new val create(id': USize) => id = id'
  fun eq(that: Var): Bool => id == that.id
  fun string(): String => "#(" + id.string() + ")"
  fun hash(): U64 => id.hash()

class val Pair
  let fst: Term
  let snd: Term

  new val create(f: Term, s: Term) =>
    fst = f
    snd = s

  fun string(): String =>
    "(" + fst.string() + " . " + snd.string() + ")"

// Mimic lists of terms
// e.g. "a b c" is converted into Pair("a", Pair("b", Pair("c", "")))
primitive TList
  fun apply(str: String): Term =>
    let arr = str.split(" ")
    var n = arr.size()
    var l: Term = ""
    try
      while n > 0 do
        l = Pair(arr(n - 1), l)
        n = n - 1
      end
      match l
      | let p: Pair => p
      else
        Pair(l, "")
      end
    else
      ""
    end

class val SubstEnv
  let _s: pers.Map[Var, Term]

  new val create(mp: pers.Map[Var, Term] val =
    pers.Map[Var, Term])
  =>
    _s = mp

  fun empty(): Bool => _s.size() == 0
  fun add(v: Var, t: Term): SubstEnv => SubstEnv(_s.update(v, t))
  fun apply(v: Var): Term => _s.get_or_else(v, v)

  fun string(): String =>
    var str = ""
    for (v, t) in _s.pairs() do
      // USize.max_value() is used to record a #t (this is a hack). Don't print
      if not (v.id == USize.max_value()) then
        str = str + " (" + v.string() + " . " + t.string() + ")"
      end
    end
    str

class val State
  let subst_env: SubstEnv
  let next_var_id: USize

  new val create(s: SubstEnv = SubstEnv, next_v_id: USize = 0) =>
    subst_env = s
    next_var_id = next_v_id

  fun string(): String =>
    "((" + subst_env.string() + ")" + " . " + next_var_id.string() + ")"

primitive MK
  fun walk(t: Term, s: SubstEnv): Term =>
    match t
    | let v: Var => s(v)
    else t end

  fun ext_s(v: Var, t: Term, s: SubstEnv): SubstEnv =>
    s + (v, t)

  fun unify(u: Term, v: Term, s: SubstEnv): SubstEnv
  =>
    let uw = walk(u, s)
    let vw = walk(v, s)
    match (uw, vw)
    | (let x: Var, let y: Var) if x == y => s
    | (let x: Var, _) => ext_s(x, v, s)
    | (_, let y: Var) => ext_s(y, u, s)
    | (let p1: Pair, let p2: Pair) =>
      let s' = unify(p1.fst, p2.fst, s)
      unify(p1.snd, p2.snd, s')
    | (let x: Value, let y: Value) if x == y =>
      // A hack to record #t
      s + (Var(USize.max_value()), "#t")
    else
      SubstEnv
    end

  fun mzero(): Stream[State] =>
    SNil[State]

  fun unit(s: State): Stream[State] =>
    SCons[State](s, mzero())

  // ===
  fun u_u(u: Term, v: Term): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        let s = MK.unify(u, v, sc.subst_env)
        if s.empty() then
          MK.mzero()
        else
          MK.unit(State(s, sc.next_var_id))
        end
    end

  fun call_fresh(f: GoalConstructor): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        let v_id = sc.next_var_id
        let g = f(Var(v_id))
        g(State(sc.subst_env, v_id + 1))
    end

  fun mplus(s1: Stream[State], s2: Stream[State]):
    Stream[State]
  =>
    try
      match s1
      | let n: SNil[State] => s2
      | let sn: SNext[State] =>
        SMerge[State](s2, sn.force())
      else
        SCons[State](s1.head(), mplus(s1.tail(), s2))
      end
    else
      mzero()
    end

  fun bind(s: Stream[State], g: Goal): Stream[State] =>
    try
      match s.force()
      | let n: SNil[State] => mzero()
      else
        mplus(g(s.head()), bind(s.tail(), g))
      end
    else
      mzero()
    end

  // We don't need to call disj and conj directly since
  // or and and have default implementations on the Goal trait.
  fun disj(g1: Goal, g2: Goal): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        MK.mplus(g1(sc), g2(sc))
    end

  fun conj(g1: Goal, g2: Goal): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        MK.bind(g1(sc), g2)
    end

  fun conso(a: Term, b: Term, c: Term): Goal =>
    u_u(Pair(a, b), c)

  fun nullo(a: Term): Goal =>
    u_u("", a)

  fun empty_goal(): Goal =>
    object val is Goal
      fun apply(s: State): Stream[State] =>
        SNil[State]
    end

  ///////////////////////////////////////////////////////////////////////////
  // Instead of macros, creating different versions of fresh
  ///////////////////////////////////////////////////////////////////////////
  fun fresh2(f: GoalConstructor2): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        let v_id1 = sc.next_var_id
        let v_id2 = v_id1 + 1
        let g = f(Var(v_id1), Var(v_id2))
        g(State(sc.subst_env, v_id2 + 1))
    end

  fun fresh3(f: GoalConstructor3): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        let v_id1 = sc.next_var_id
        let v_id2 = v_id1 + 1
        let v_id3 = v_id2 + 1
        let g = f(Var(v_id1), Var(v_id2), Var(v_id3))
        g(State(sc.subst_env, v_id3 + 1))
    end

  fun fresh4(f: GoalConstructor4): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        let v_id1 = sc.next_var_id
        let v_id2 = v_id1 + 1
        let v_id3 = v_id2 + 1
        let v_id4 = v_id3 + 1
        let g = f(Var(v_id1), Var(v_id2), Var(v_id3), Var(v_id4))
        g(State(sc.subst_env, v_id4 + 1))
    end

trait val Goal
  fun apply(state: State = State): Stream[State]

  fun val op_or(that: Goal): Goal => MK.disj(this, that)
  fun val op_and(that: Goal): Goal => MK.conj(this, that)

type GoalConstructor is {(Var): Goal} val
type GoalConstructor2 is {(Var, Var): Goal} val
type GoalConstructor3 is {(Var, Var, Var): Goal} val
type GoalConstructor4 is {(Var, Var, Var, Var): Goal} val





