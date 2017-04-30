/////////////////////
// Pattern matching
/////////////////////
primitive PAny is Pattern
  fun string(): String => "*_*"
  fun val merge(t: Term): Term => t

class val PList is Pattern
  let _l: Pair
  new val create(l: Pair) => _l = l
  fun string(): String => "*(" + _l.string() + ")*"
  fun val merge(t: Term): Term ? =>
    match t
    | let pany: PAny => this
    | let plist: PList => merge(plist._l)
    | let p: Pair =>
      var still_pattern = false
      var acc = Array[Term]
      var pattern = _l
      var matched = p
      while true do
        match (pattern.fst, matched.fst)
        | (let p1: PAny, let t2: Term) => acc.push(t2)
        | (let t1: Term, let p2: PAny) => acc.push(t1)
        | (let p1: Pattern, let t2: Term) =>
          acc.push(p1.merge(t2))
        | (let t1: Term, let p2: Pattern) =>
          acc.push(p2.merge(t1))
        | (let v1: Vl, let v2: Vl) if v1.valeq(v2) => acc.push(v1)
        | (let p1: Pair, let p2: Pair) =>
          acc.push(Patterns.merge_pairs(p1, p2))
        | (let v1: Var, let t2: Term) => acc.push(t2)
        | (let t1: Term, let v2: Var) => acc.push(t1)
        else
          error
        end
        match (pattern.snd, matched.snd)
        | (let x: Vl, let y: Vl) if x.valeq(y) =>
          return Patterns.construct(acc, x)
        | (let x: Pair, let y: Pair) =>
          pattern = x
          matched = y
        | (let p1: PAny, let t2: Term) =>
          return Patterns.construct(acc, t2)
        | (let t1: Term, let p2: PAny) =>
          return Patterns.construct(acc, t1)
        | (let x: Pattern, let t2: Term) =>
          return Patterns.construct(acc, x.merge(t2))
        | (let t1: Term, let y: Pattern) =>
          return Patterns.construct(acc, y.merge(t1))
        | (let v1: Var, let t2: Term) =>
          return Patterns.construct(acc, v1)
        | (let t1: Term, let v2: Var) =>
          return Patterns.construct(acc, v2)
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
      match p.merge(m)
      | let t: Term =>
        var subst_env = s + (Var(True.id()), True())
        match t1
        | let v: Var => subst_env = subst_env + (v, t)
        end
        match t2
        | let v: Var => subst_env = subst_env + (v, t)
        end
        subst_env
      else
        SubstEnv
      end
    else
      SubstEnv
    end

  fun merge_pairs(p1: Pair, p2: Pair): Term ? =>
    _merge_pairs(p1, p2, Array[Term])

  fun _merge_pairs(t1: Term, t2: Term, acc: Array[Term]): Term ?
  =>
    match (t1, t2)
    | (let p1: Pair, let p2: Pair) =>
      match (p1.fst, p2.fst)
      | (let v1: Vl, let v2: Vl) if v1.valeq(v2) => acc.push(v1)
      | (let pair1: Pair, let pair2: Pair) =>
        acc.push(_merge_pairs(pair1, pair2, acc))
      | (let pat: Pattern, let t: Term) =>
        acc.push(pat.merge(t))
      | (let t: Term, let pat: Pattern) =>
        acc.push(pat.merge(t))
      else
        error
      end
      _merge_pairs(p1.snd, p2.snd, acc)
    | (let term1: Term, let term2: Term) =>
      let terminal: Term =
        match (term1, term2)
        | (let v1: Vl, let v2: Vl) if v1.valeq(v2) => v1
        | (let pair1: Pair, let pair2: Pair) => _merge_pairs(pair1, pair2, acc)
        | (let pat: Pattern, let t: Term) => pat.merge(t)
        | (let t: Term, let pat: Pattern) => pat.merge(t)
        else
          error
        end
      construct(acc, terminal)
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
      match (p.fst, p.snd)
      | (let pat: Pattern, _) => true
      | (_, let pat: Pattern) => true
      | (let pair1: Pair, let pair2: Pair) =>
        Patterns.is_pattern(pair1) or Patterns.is_pattern(pair2)
      | (let pair: Pair, _) =>
        Patterns.is_pattern(pair)
      | (_, let pair: Pair) =>
        Patterns.is_pattern(pair)
      else
        false
      end
    else
      false
    end
