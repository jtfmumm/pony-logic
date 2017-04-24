use "collections"
use pers = "collections/persistent"

type Value is String
type Term is (Value val | Var val | Pair val)

class Var is Equatable[Var val]
  let id: USize
  new val create(id': USize) => id = id'
  fun eq(that: box->Var val): Bool => id == that.id
  fun string(): String => "#(" + id.string() + ")"
  fun hash(): U64 => id.hash()

class Pair
  let fst: Term val
  let snd: Term val

  new val create(f: Term val, s: Term val) =>
    fst = f
    snd = s

  fun string(): String =>
    "(" + fst.string() + " . " + snd.string() + ")"

// Mimic lists of terms
// e.g. "a b c" is converted into Pair("a", Pair("b", Pair("c", "")))
primitive TList
  fun apply(str: String): Term val =>
    let arr = str.split(" ")
    var n = arr.size()
    var l: Term val = ""
    try
      while n > 0 do
        l = Pair(arr(n - 1), l)
        n = n - 1
      end
      match l
      | let p: Pair val => p
      else
        Pair(l, "")
      end
    else
      ""
    end

class SubstEnv
  let _s: pers.Map[Var val, Term val]

  new val create(mp: pers.Map[Var val, Term val] val =
    pers.Map[Var val, Term val])
  =>
    _s = mp

  fun is_empty(): Bool =>
    _s.size() == 0

  fun add(v: Var val, t: Term val): SubstEnv val =>
    SubstEnv(_s.update(v, t))

  fun string(): String =>
    var str = ""
    for (v, t) in _s.pairs() do
      if not (v.id == USize.max_value()) then
        str = str + " (" + v.string() + " . " + t.string() + ")"
      end
    end
    str

  fun substitute(v: Var val): Term val =>
    try
      if _s.contains(v) then
        _s(v)
      else
        v
      end
    else
      v
    end

class State
  let subst_env: SubstEnv val
  let next_var_id: USize

  new val create(s: SubstEnv val, next_v_id: USize = 0) =>
    subst_env = s
    next_var_id = next_v_id

  fun string(): String =>
    "((" + subst_env.string() + ")" + " . " + next_var_id.string() + ")"

primitive MK
  fun walk(t: Term val, s: SubstEnv val): Term val =>
    match t
    | let v: Var val =>
      s.substitute(v)
    else
      t
    end

  fun ext_s(v: Var val, t: Term val, s: SubstEnv val): SubstEnv val =>
    s.add(v, t)

  fun unify(u: Term val, v: Term val, s: SubstEnv val): SubstEnv val
  =>
    let uw = walk(u, s)
    let vw = walk(v, s)
    match (uw, vw)
    | (let x: Var val, let y: Var val) if x == y => s
    | (let x: Var val, _) => ext_s(x, v, s)
    | (_, let y: Var val) => ext_s(y, u, s)
    | (let p1: Pair val, let p2: Pair val) =>
      let s' = unify(p1.fst, p2.fst, s)
      unify(p1.snd, p2.snd, s')
    | (let x: Value val, let y: Value val) if x == y =>
      // A hack to record #t
      s.add(Var(USize.max_value()), "#t")
    else
      SubstEnv
    end

  fun mzero(): Stream[State val] val =>
    SNil[State val]

  fun unit(s: State val): Stream[State val] val =>
    SCons[State val](s, mzero())

  fun u_u(u: Term val, v: Term val): Goal val =>
    let mk = MK
    recover
      {(sc: State val)(mk, u, v): Stream[State val] val =>
        let s = mk.unify(u, v, sc.subst_env)
        if s.is_empty() then
          mk.mzero()
        else
          mk.unit(State(s, sc.next_var_id))
        end
      }
    end

  fun call_fresh(f: GoalConstructor val): Goal val =>
    recover
      {(sc: State val)(f): Stream[State val] val =>
        let v_id = sc.next_var_id
        let g = f(Var(v_id))
        g(State(sc.subst_env, v_id + 1))
      }
    end

  fun mplus(s1: Stream[State val] val, s2: Stream[State val] val):
    Stream[State val] val
  =>
    try
      match s1
      | let n: SNil[State val] val => s2
      | let sn: SNext[State val] val =>
        SMerge[State val](s2, sn.force())
      else
        SCons[State val](s1.head(), mplus(s1.tail(), s2))
      end
    else
      mzero()
    end

  fun bind(s: Stream[State val] val, g: Goal val): Stream[State val] val =>
    try
      match s.force()
      | let n: SNil[State val] val => mzero()
      else
        mplus(g(s.head()), bind(s.tail(), g))
      end
    else
      mzero()
    end

  fun disj(g1: Goal val, g2: Goal val): Goal val =>
    let mk = MK
    recover
      {(sc: State val)(mk): Stream[State val] val =>
        mk.mplus(g1(sc), g2(sc))
      }
    end

  fun conj(g1: Goal val, g2: Goal val): Goal val =>
    let mk = MK
    recover
      {(sc: State val)(mk): Stream[State val] val =>
        mk.bind(g1(sc), g2)
      }
    end

  ///////////////////////////////////////////////////////////////////////////
  // Instead of macros, creating different versions of fresh, conj, and disj
  ///////////////////////////////////////////////////////////////////////////
  fun fresh2(f: GoalConstructor2 val): Goal val =>
    recover
      {(sc: State val)(f): Stream[State val] val =>
        let v_id1 = sc.next_var_id
        let v_id2 = v_id1 + 1
        let g = f(Var(v_id1), Var(v_id2))
        g(State(sc.subst_env, v_id2 + 1))
      }
    end

  fun fresh3(f: GoalConstructor3 val): Goal val =>
    recover
      {(sc: State val)(f): Stream[State val] val =>
        let v_id1 = sc.next_var_id
        let v_id2 = v_id1 + 1
        let v_id3 = v_id2 + 1
        let g = f(Var(v_id1), Var(v_id2), Var(v_id3))
        g(State(sc.subst_env, v_id3 + 1))
      }
    end

  fun fresh4(f: GoalConstructor4 val): Goal val =>
    recover
      {(sc: State val)(f): Stream[State val] val =>
        let v_id1 = sc.next_var_id
        let v_id2 = v_id1 + 1
        let v_id3 = v_id2 + 1
        let v_id4 = v_id3 + 1
        let g = f(Var(v_id1), Var(v_id2), Var(v_id3), Var(v_id4))
        g(State(sc.subst_env, v_id4 + 1))
      }
    end

  fun disj3(g1: Goal val, g2: Goal val, g3: Goal val): Goal val =>
    let mk = MK
    disj(g1,
      recover
        {(sc: State val)(mk): Stream[State val] val =>
          mk.mplus(g2(sc), g3(sc))
        }
      end
    )

  fun disj4(g1: Goal val, g2: Goal val, g3: Goal val, g4: Goal val): Goal val
  =>
    let mk = MK
    disj(g1,
      disj(g2,
        recover
          {(sc: State val)(mk): Stream[State val] val =>
            mk.mplus(g3(sc), g4(sc))
          }
        end
      )
    )

  fun disj5(g1: Goal val, g2: Goal val, g3: Goal val, g4: Goal val,
    g5: Goal val): Goal val
  =>
    let mk = MK
    disj(g1,
      disj(g2,
        disj(g3,
          recover
            {(sc: State val)(mk): Stream[State val] val =>
              mk.mplus(g4(sc), g5(sc))
            }
          end
        )
      )
    )

  fun conj3(g1: Goal val, g2: Goal val, g3: Goal val): Goal val =>
    let mk = MK
    conj(g1,
      recover
        {(sc: State val)(mk): Stream[State val] val =>
          mk.bind(g2(sc), g3)
        }
      end
    )

  fun conj4(g1: Goal val, g2: Goal val, g3: Goal val, g4: Goal val): Goal val
  =>
    let mk = MK
    conj(g1,
      conj(g2,
        recover
          {(sc: State val)(mk): Stream[State val] val =>
            mk.bind(g3(sc), g4)
          }
        end
      )
    )

  fun conj5(g1: Goal val, g2: Goal val, g3: Goal val, g4: Goal val,
    g5: Goal val): Goal val
  =>
    let mk = MK
    conj(g1,
      conj(g2,
        conj(g3,
          recover
            {(sc: State val)(mk): Stream[State val] val =>
              mk.bind(g4(sc), g5)
            }
          end
        )
      )
    )

  fun conde(gs: Array[Array[Goal val]]): Goal val =>
    """
    A hack to emulate the conde macro. Can accept 5 arrays which
    can consist of 5 goals each.
    """
    try
      match gs.size()
      | 1 => _pick_conj(gs(0))
      | 2 => disj(_pick_conj(gs(0)), _pick_conj(gs(1)))
      | 3 => disj3(_pick_conj(gs(0)), _pick_conj(gs(1)), _pick_conj(gs(2)))
      | 4 => disj4(_pick_conj(gs(0)), _pick_conj(gs(1)), _pick_conj(gs(2)),
                   _pick_conj(gs(3)))
      | 5 => disj5(_pick_conj(gs(0)), _pick_conj(gs(1)), _pick_conj(gs(2)),
                   _pick_conj(gs(3)), _pick_conj(gs(4)))
      else
        empty_goal()
      end
    else
      empty_goal()
    end

  fun _pick_conj(gs: Array[Goal val]): Goal val =>
    try
      match gs.size()
      | 1 => gs(0)
      | 2 => conj(gs(0), gs(1))
      | 3 => conj3(gs(0), gs(1), gs(2))
      | 4 => conj4(gs(0), gs(1), gs(2), gs(3))
      | 5 => conj5(gs(0), gs(1), gs(2), gs(3), gs(4))
      else
        empty_goal()
      end
    else
      empty_goal()
    end

  fun empty_state(): State val =>
    State(SubstEnv, 0)

  fun conso(a: Term, b: Term, c: Term): Goal val =>
    u_u(Pair(a, b), c)

  fun nullo(a: Term): Goal val =>
    u_u("", a)

  fun empty_goal(): Goal val =>
    recover
      {(s: State val): Stream[State val] val =>
        SNil[State val]
      }
    end

type Goal is {(State val): Stream[State val] val}
type GoalConstructor is {(Var val): Goal val}
type GoalConstructor2 is {(Var val, Var val): Goal val}
type GoalConstructor3 is {(Var val, Var val, Var val): Goal val}
type GoalConstructor4 is {(Var val, Var val, Var val, Var val): Goal val}





