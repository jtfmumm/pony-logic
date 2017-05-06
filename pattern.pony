/////////////////////
// Pattern matching
/////////////////////
primitive PAny is Pattern
  fun string(): String => "*_*"
  fun val merge(t: Term, s: SubstEnv): (Term, SubstEnv) => (t, s)

class val PList is Pattern
  let _l: Pair
  new val create(l: Pair) =>
    _l =
      match l.snd
      | let p: Pair =>
        if Patterns.is_pattern(p) then
          Pair(l.fst, PList(p))
        else
          l
        end
      else l end
  fun string(): String => "*(" + _l.string() + ")*"
  fun val merge(t: Term, s: SubstEnv): (Term, SubstEnv) ? =>
    match t
    | let v: Var => (v, MK.unify(v, this, s))
    | let pany: PAny => (this, s)
    | let plist: PList => merge(plist._l, s)
    | let p: Pair =>
      var s': SubstEnv = s
      var acc = Array[Term]
      var pattern = _l
      var matched = p
      while true do
        match (pattern.fst, matched.fst)
        | (let p1: PAny, let t2: Term) =>
          @printf[I32]("PAny!!\n".cstring())
          acc.push(t2)
        | (let t1: Term, let p2: PAny) => acc.push(t1)
        | (let p1: Pattern, let t2: Term) =>
          (let t': Term, s') = p1.merge(t2, s')
          acc.push(t')
        | (let t1: Term, let p2: Pattern) =>
          (let t': Term, s') = p2.merge(t1, s')
          acc.push(t')
        | (let v1: Vl, let v2: Vl) if v1.valeq(v2) => acc.push(v1)
        | (let p1: Pair, let p2: Pair) =>
          (let t': Term, s') = Patterns.merge_pairs(p1, p2, s')
          acc.push(t')
        | (let v1: Var, let t2: Term) =>
          s' = MK.unify(v1, t2, s')
          acc.push(t2)
        | (let t1: Term, let v2: Var) =>
          s' = MK.unify(t1, v2, s')
          @printf[I32]("%s!!\n".cstring(), t1.string().cstring())
          acc.push(t1)
        else
          error
        end
        @printf[I32]("!! Snds: %s <-> %s\n".cstring(),
          pattern.snd.string().cstring(), matched.snd.string().cstring())
        match (pattern.snd, matched.snd)
        | (let x: Vl, let y: Vl) if x.valeq(y) =>
          @printf[I32]("%s <-> %s\n".cstring(), x.string().cstring(),
            y.string().cstring())
          return (Patterns.construct(acc, x), s')
        | (let x: Pair, let y: Pair) =>
          pattern = x
          matched = y
        | (let p1: PAny, let t2: Term) =>
          return (Patterns.construct(acc, t2), s')
        | (let t1: Term, let p2: PAny) =>
          return (Patterns.construct(acc, t1), s')
        | (let x: Pattern, let t2: Term) =>
          (let t': Term, s') = x.merge(t2, s')
          return (Patterns.construct(acc, t'), s')
        | (let t1: Term, let y: Pattern) =>
          (let t': Term, s') = y.merge(t1, s')
          return (Patterns.construct(acc, t'), s')
        | (let v1: Var, let t2: Term) =>
          s' = MK.unify(v1, t2, s')
          return (Patterns.construct(acc, v1), s')//t2), s')//
        | (let t1: Term, let v2: Var) =>
          s' = MK.unify(t1, v2, s')
          return (Patterns.construct(acc, v2), s')//t1), s')//
        else
          error
        end
      end
      error
    else
      error
    end

primitive Patterns
  fun apply(p: Pattern, m: Term, t1: Term, t2: Term, s: SubstEnv): SubstEnv =>
    try
      @printf[I32]("Patternific!! %s <-> %s\n".cstring(), p.string().cstring(),
        m.string().cstring())
      (let merged: Term, let s': SubstEnv) = p.merge(m, s)
      match merged
      | let t: Term =>
        @printf[I32]("Term!!\n".cstring())
        var subst_env = MK.ext_s(Var(True.id()), True(), s')
        match t1
        | let v: Var => subst_env = MK.ext_s(v, t, subst_env)
        end
        match t2
        | let v: Var => subst_env = MK.ext_s(v, t, subst_env)
        end
        subst_env
      else
        SubstEnv
      end
    else
      SubstEnv
    end

  fun merge_pairs(p1: Pair, p2: Pair, s: SubstEnv): (Term, SubstEnv) ? =>
    _merge_pairs(p1, p2, Array[Term], s)

  fun _merge_pairs(t1: Term, t2: Term, acc: Array[Term], s: SubstEnv):
    (Term, SubstEnv) ?
  =>
    var s' = s
    match (t1, t2)
    | (let p1: Pair, let p2: Pair) =>
      match (p1.fst, p2.fst)
      | (let v1: Vl, let v2: Vl) if v1.valeq(v2) => acc.push(v1)
      | (let pair1: Pair, let pair2: Pair) =>
        (let t': Term, s') = _merge_pairs(pair1, pair2, acc, s')
        acc.push(t')
      | (let pat: Pattern, let t: Term) =>
        (let t': Term, s') = pat.merge(t, s')
        acc.push(t')
      | (let t: Term, let pat: Pattern) =>
        (let t': Term, s') = pat.merge(t, s')
        acc.push(t')
      else
        error
      end
      _merge_pairs(p1.snd, p2.snd, acc, s')
    | (let term1: Term, let term2: Term) =>
      (let terminal: Term, s') =
        match (term1, term2)
        | (let v1: Vl, let v2: Vl) if v1.valeq(v2) => (v1, s')
        | (let pair1: Pair, let pair2: Pair) =>
          _merge_pairs(pair1, pair2, acc, s')
        | (let pat: Pattern, let t: Term) => pat.merge(t, s')
        | (let t: Term, let pat: Pattern) => pat.merge(t, s')
        else
          error
        end
      (construct(acc, terminal), s)//s')
    else
      error
    end

  fun construct(acc: Array[Term], terminal: Term): Term ? =>
    var n = acc.size()
    var result: Term = terminal
    while n > 0 do
      result = Pair(acc(n - 1), result)
      n = n - 1
    end
    if Patterns.is_pattern(result) then
      PList(result as Pair)
    else
      result
    end

  fun is_pattern(t: Term): Bool =>
    match t
    | let pat: Pattern => true
    | let vl: Vl => false
    | let p: Pair =>
      is_pattern(p.fst) or is_pattern(p.snd)
    else
      false
    end
