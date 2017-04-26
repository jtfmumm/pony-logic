use "collections"
// use pers = "collections/persistent"

type Value is String
type Term is (Value | Var | Pair)

class val Var is Equatable[Var]
  let id: USize
  new val create(id': USize) => id = id'
  fun eq(that: Var): Bool => id == that.id
  fun string(): String => "#(" + id.string() + ")"
  fun hash(): U64 => id.hash()
  fun increment(): Var => Var(id + 1)

class val Pair
  let fst: Term
  let snd: Term

  new val create(f: Term, s: Term) =>
    fst = f
    snd = s

  fun string(): String =>
    "(" + fst.string() + " . " + snd.string() + ")"

primitive TNil
  fun apply(): String =>
    "()"

// Mimic lists of terms
// e.g. "a b c" is converted into Pair("a", Pair("b", Pair("c", "")))
primitive TList
  fun apply(str: String): Term =>
    let arr = str.split(" ")
    var n = arr.size()
    if (str == "") or (n == 0) then return TNil() end
    var l: Term = TNil()
    try
      while n > 0 do
        l = Pair(arr(n - 1), l)
        n = n - 1
      end
      match l
      | let p: Pair => p
      else
        TNil()
      end
    else
      // This should never happen
      TNil()
    end

class val SubstEnv
  // There's a bug in the Pony stdlib CHAMP map.
  // TODO: Update and use my HAMT map for now and address Pony stdlib bug
  // Temporarily using a very inefficient persistent map standin
  let _s: PMap

  new val create(mp: PMap = PMap) =>
    _s = mp

  fun empty(): Bool => _s.size() == 0
  fun add(v: Var, t: Term): SubstEnv => SubstEnv(_s.update(v, t))
  fun apply(v: Var): Term => _s.get_or_else(v, v)
  fun reify(v: Var): Term => MK.walk(v, SubstEnv(_s))._1

  fun string(): String =>
    var str = ""
    for (v, t) in _s.map().pairs() do
      // USize.max_value() is used to record a #t (this is a hack). Don't print
      if not (v.id == USize.max_value()) then
        str = str + " (" + v.string() + " . " + t.string() + ")"
        // str = str + "\n  " + v.string() + ": " + t.string()
      end
    end
    str

class val State
  let subst_env: SubstEnv
  let next_var_id: USize

  new val create(s: SubstEnv = SubstEnv, next_v_id: USize = 0) =>
    subst_env = s
    next_var_id = next_v_id

  fun apply(v: Var): Term => subst_env(v)
  fun reify(v: Var): Term => subst_env.reify(v)

  fun string(): String =>
    "((" + subst_env.string() + ")" + " . " + next_var_id.string() + ")"
    // "\nState(" + subst_env.string() + ")" + "\nNext var: " +
      // next_var_id.string() + ")"

primitive MK
  fun walk(t: Term, s: SubstEnv): (Term, SubstEnv) =>
    match t
    | let v: Var =>
      match s(v)
      | let v': Var if v != v' =>
        (let next_t: Term, let next_s: SubstEnv) = walk(v', s)
        (next_t, next_s)
      | let p: Pair =>
        match (p.fst, p.snd)
        | (let v1: Var, let v2: Var) =>
          (let fst: Term, let s': SubstEnv) = walk(v1, s)
          (let snd: Term, let s'': SubstEnv) = walk(v2, s')
          (Pair(fst, snd), s'')
        | (let v1: Var, _) =>
          (let fst: Term, let s': SubstEnv) = walk(v1, s)
          (Pair(fst, p.snd), s')
        | (_, let v2: Var) =>
          (let snd: Term, let s': SubstEnv) = walk(v2, s)
          (Pair(p.fst, snd), s')
        else (p, s) end
      else (s(v), s) end
    else (t, s) end

  fun ext_s(v: Var, t: Term, s: SubstEnv): SubstEnv =>
    s + (v, t)

  fun unify(u: Term, v: Term, s: SubstEnv): SubstEnv =>
    (let uw: Term, let s': SubstEnv) = walk(u, s)
    (let vw: Term, let s'': SubstEnv) = walk(v, s')
    match (uw, vw)
    | (let x: Var, let y: Var) if x == y => s''
    | (let x: Var, _) => ext_s(x, v, s'')
    | (_, let y: Var) => ext_s(y, u, s'')
    | (let p1: Pair, let p2: Pair) =>
      let ps = unify(p1.fst, p2.fst, s'')
      unify(p1.snd, p2.snd, ps)
    | (let x: Value, let y: Value) if x == y =>
      // A hack to record #t
      s'' + (Var(USize.max_value()), "#t")
    // | (let x: TNil, let y: TNil) if x == y =>
    //   // A hack to record #t
    //   s'' + (Var(USize.max_value()), "#t")
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

  fun mplus(s1: Stream[State], s2: Stream[State]): Stream[State] =>
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

  fun delay(g: Goal): Goal =>
    object val is Goal
      let g: Goal = g
      fun apply(s: State): Stream[State] =>
        SDelay[State]({(): Stream[State] => g(s)} val)
    end

  fun conso(a: Term, b: Term, c: Term): Goal =>
    u_u(Pair(a, b), c)

  fun heado(h: Term, l: Term): Goal =>
    call_fresh(
      {(t: Var): Goal =>
        MK.conso(h, t, l)
      } val)

  fun tailo(t: Term, l: Term): Goal =>
    call_fresh(
      {(h: Var): Goal =>
        MK.conso(h, t, l)
      } val)

  fun appendo(l1: Term, l2: Term, result: Term): Goal =>
    (nullo(l1) and u_u(l2, result)) or
    fresh3(
      {(h: Var, t: Var, lst: Var): Goal =>
        MK.conso(h, t, l1) and
        MK.conso(h, lst, result) and
        MK.appendo(t, l2, lst)
      } val)

  fun membero(x: Term, l: Term): Goal =>
    call_fresh(
      {(t: Var): Goal =>
        MK.conso(x, t, l)
      } val)
    or fresh2(
      {(h: Var, t: Var)(x): Goal =>
        MK.delay(
          MK.delay(MK.conso(h, t, l)) and
          MK.delay(MK.membero(x, t))
        )
      } val)

  fun match_elemento(x: Term, y: Term): Goal =>
    u_u(x, y) or
    u_u(x, "_")

  fun match_conso(a: Term, b: Term, c: Term): Goal =>
    u_u(Pair(a, b), c) or
    call_fresh(
      {(h: Var): Goal =>
        MK.u_u(a, "_") and
          MK.conso(h, b, c)
      } val)

  fun match_heado(h: Term, l: Term): Goal =>
    fresh2(
      {(t: Var, h2: Var): Goal =>
        MK.conso(h, t, l) or
        (MK.conso(h2, t, l) and
          MK.u_u(h, "_"))
      } val)

  fun match_membero(x: Term, l: Term): Goal =>
    call_fresh(
      {(t: Var): Goal =>
        MK.match_conso(x, t, l)
      } val)
    or fresh2(
      {(h: Var, t: Var)(x): Goal =>
        MK.delay(
          MK.delay(MK.match_conso(h, t, l)) and
          MK.delay(MK.match_membero(x, t))
        )
      } val)

  fun match_listo(l1: Term, l2: Term): Goal =>
    (nullo(l1) and nullo(l2)) or
    fresh4(
      {(h1: Var, h2: Var, t1: Var, t2: Var): Goal =>
        MK.conso(h1, t1, l1) and
        MK.conso(h2, t2, l2) and
        MK.match_elemento(h1, h2) and
        MK.match_listo(t1, t2)
      } val)

  fun matcho(t1: Term, t2: Term): Goal =>
    match_elemento(t1, t2) or
    match_listo(t1, t2)

  fun nullo(a: Term): Goal =>
    u_u(TNil(), a)

  fun empty_goal(): Goal =>
    object val is Goal
      fun apply(s: State): Stream[State] =>
        SNil[State]
    end

  fun reify_items(st: Stream[State]): Stream[Term] =>
    Streams[State].map[Term]({(s: State): Term =>
      s.reify(Var(0))} val, st)

  fun reify(st: Stream[State]): Stream[String] =>
    Streams[State].map[String]({(s: State): String =>
      "\n[0: " + s.reify(Var(0)).string() + "]"} val, st)

  fun reify2(st: Stream[State]): Stream[String] =>
    Streams[State].map[String]({(s: State): String =>
      "\n[0: " + s.reify(Var(0)).string() + ", 1: " +
        s.reify(Var(1)).string() + "]"} val, st)

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

class val Relation
  let _ts: ReadSeq[(Term, Term)] val

  new val create(ts: ReadSeq[(Term, Term)] val) =>
    _ts = ts

  fun apply(t1: Term, t2: Term): Goal =>
    var n = _ts.size()
    var g = MK.empty_goal()
    try
      while n > 0 do
        let next = _ts(n - 1)
        g = (MK.u_u(next._1, t1) and MK.u_u(next._2, t2)) or g
        n = n - 1
      end
    end
    g

class val TransitiveRelation
  let _f: {(Term, Term): Goal} val

  new create(ts: ReadSeq[(Term, Term)] val) =>
    let r = Relation(ts)
    _f = Transitive(object val
      fun apply(t1: Term, t2: Term): Goal =>
        r(t1, t2)
    end)

  fun apply(t1: Term, t2: Term): Goal =>
    _f(t1, t2)

primitive Transitive
  fun apply(f: {(Term, Term): Goal} val): {(Term, Term): Goal} val =>
    object val
      let f: {(Term, Term): Goal} val = f
      fun apply(t1: Term, t2: Term): Goal =>
        _Transitive(t1, t2, f)
    end

primitive _Transitive
  fun apply(t1: Term, t2: Term, f: {(Term, Term): Goal} val): Goal =>
    MK.fresh2(
      {(q1: Var, q2: Var): Goal =>
        f(t1, t2) or
        (f(t1, q1) and _Transitive(q1, t2, f))
      } val)


// This is an inefficient substitute for a persistent map, copying everything
// on any update.
// It exists because there's a bug in the Pony stdlib persistent map
// that either causes keys to be lost or pairs() to return an incomplete
// iterator. Once that is addressed, or I update my HAMT map to work with
// latest compiler, stop using this.
class val PMap
  let _s: Map[Var, Term] val

  new val create(s: Map[Var, Term] val = recover Map[Var, Term] end) =>
    _s = s

  fun size(): USize => _s.size()

  fun update(v: Var, t: Term): PMap =>
    let m: Map[Var, Term] trn = recover Map[Var, Term] end
    for (k, v') in _s.pairs() do
      m(k) = v'
    end
    m(v) = t
    PMap(consume m)

  fun get_or_else(v: Var, t: Term): Term =>
    _s.get_or_else(v, t)

  fun map(): Map[Var, Term] val => _s
