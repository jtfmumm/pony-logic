use "collections"
use pers = "collections/persistent"

type Value is String
type Term is (Value | Var | Pair)

class val Var is Equatable[Var]
  let id: USize
  new val create(id': USize) => id = id'
  fun eq(that: box->Var): Bool => id == that.id
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

  fun is_empty(): Bool =>
    _s.size() == 0

  fun add(v: Var, t: Term): SubstEnv =>
    SubstEnv(_s.update(v, t))

  fun string(): String =>
    var str = ""
    for (v, t) in _s.pairs() do
      // USize.max_value() is used to record a #t (this is a hack). Don't print
      if not (v.id == USize.max_value()) then
        str = str + " (" + v.string() + " . " + t.string() + ")"
      end
    end
    str

  fun substitute(v: Var): Term =>
    _s.get_or_else(v, v)

class val State
  let subst_env: SubstEnv
  let next_var_id: USize

  new val create(s: SubstEnv, next_v_id: USize = 0) =>
    subst_env = s
    next_var_id = next_v_id

  fun string(): String =>
    "((" + subst_env.string() + ")" + " . " + next_var_id.string() + ")"

primitive MK
  fun walk(t: Term, s: SubstEnv): Term =>
    match t
    | let v: Var =>
      s.substitute(v)
    else
      t
    end

  fun ext_s(v: Var, t: Term, s: SubstEnv): SubstEnv =>
    s.add(v, t)

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
      s.add(Var(USize.max_value()), "#t")
    else
      SubstEnv
    end

  fun mzero(): Stream[State] =>
    SNil[State]

  fun unit(s: State): Stream[State] =>
    SCons[State](s, mzero())

  // ===
  fun u_u(u: Term, v: Term): Goal =>
    let mk = MK
    recover
      {(sc: State)(mk, u, v): Stream[State] =>
        let s = mk.unify(u, v, sc.subst_env)
        if s.is_empty() then
          mk.mzero()
        else
          mk.unit(State(s, sc.next_var_id))
        end
      }
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

  fun disj(g1: Goal, g2: Goal): Goal =>
    let mk = MK
    recover
      {(sc: State)(mk): Stream[State] =>
        mk.mplus(g1(sc), g2(sc))
      }
    end

  fun conj(g1: Goal, g2: Goal): Goal =>
    let mk = MK
    recover
      {(sc: State)(mk): Stream[State] =>
        mk.bind(g1(sc), g2)
      }
    end

  fun disjs(gs: ReadSeq[Goal]): Goal =>
    let mk = MK
    try
      match gs.size()
      | 0 => empty_goal()
      | 1 => gs(0)
      | 2 => disj(gs(0), gs(1))
      | let n: USize =>
        var count = n - 2
        let last_g = gs(n)
        let penultimate_g = gs(n - 1)
        var goal: Goal =
          recover
            {(sc: State)(mk, last_g, penultimate_g): Stream[State] =>
              mk.mplus(last_g(sc), penultimate_g(sc))
            }
          end
        while count > 0 do
          goal = disj(gs(count), goal)
          count = count -1
        end
        goal
      else
        empty_goal()
      end
    else
      empty_goal()
    end

  fun conjs(gs: ReadSeq[Goal]): Goal =>
    let mk = MK
    try
      match gs.size()
      | 0 => empty_goal()
      | 1 => gs(0)
      | 2 => conj(gs(0), gs(1))
      | let n: USize =>
        var count = n - 2
        let last_g = gs(n)
        let penultimate_g = gs(n - 1)
        var goal: Goal =
          recover
            {(sc: State)(mk, last_g, penultimate_g): Stream[State] =>
              mk.bind(last_g(sc), penultimate_g)
            }
          end
        while count > 0 do
          goal = conj(gs(count), goal)
          count = count -1
        end
        goal
      else
        empty_goal()
      end
    else
      empty_goal()
    end

  ///////////////////////////////////////////////////////////////////////////
  // Instead of macros, creating different versions of fresh, conj, and disj
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

  fun disj3(g1: Goal, g2: Goal, g3: Goal): Goal =>
    let mk = MK
    disj(g1,
      recover
        {(sc: State)(mk): Stream[State] =>
          mk.mplus(g2(sc), g3(sc))
        }
      end
    )

  fun disj4(g1: Goal, g2: Goal, g3: Goal, g4: Goal): Goal
  =>
    let mk = MK
    disj(g1,
      disj(g2,
        recover
          {(sc: State)(mk): Stream[State] =>
            mk.mplus(g3(sc), g4(sc))
          }
        end
      )
    )

  fun disj5(g1: Goal, g2: Goal, g3: Goal, g4: Goal,
    g5: Goal): Goal
  =>
    let mk = MK
    disj(g1,
      disj(g2,
        disj(g3,
          recover
            {(sc: State)(mk): Stream[State] =>
              mk.mplus(g4(sc), g5(sc))
            }
          end
        )
      )
    )

  fun conde(gs: Array[Array[Goal]]): Goal =>
    """
    A hack to emulate the conde macro. Can accept 5 arrays which
    can consist of 5 goals each.
    """
    try
      match gs.size()
      | 1 => conjs(gs(0))
      | 2 => disj(conjs(gs(0)), conjs(gs(1)))
      | 3 => disj3(conjs(gs(0)), conjs(gs(1)), conjs(gs(2)))
      | 4 => disj4(conjs(gs(0)), conjs(gs(1)), conjs(gs(2)),
                   conjs(gs(3)))
      | 5 => disj5(conjs(gs(0)), conjs(gs(1)), conjs(gs(2)),
                   conjs(gs(3)), conjs(gs(4)))
      else
        empty_goal()
      end
    else
      empty_goal()
    end

  fun empty_state(): State =>
    State(SubstEnv, 0)

  fun conso(a: Term, b: Term, c: Term): Goal =>
    u_u(Pair(a, b), c)

  fun nullo(a: Term): Goal =>
    u_u("", a)

  fun empty_goal(): Goal =>
    recover
      {(s: State): Stream[State] =>
        SNil[State]
      }
    end

type Goal is {(State): Stream[State]} val
type GoalConstructor is {(Var): Goal} val
type GoalConstructor2 is {(Var, Var): Goal} val
type GoalConstructor3 is {(Var, Var, Var): Goal} val
type GoalConstructor4 is {(Var, Var, Var, Var): Goal} val





