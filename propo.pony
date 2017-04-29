primitive Propo
  fun asserto(prop: Term, truth: Term, model: Term): Goal =>
    symbolo(prop)
    and
      ((MK.heado(Pair(prop, truth), model))
        or MK.fresh3(
          {(pr: Var, tr: Var, rest: Var): Goal =>
            MK.conso(Pair(pr, tr), rest, model)
              and (prop != pr)
              and (Propo.asserto(prop, truth, rest))
          } val)
    )

  fun prop_evalo(fml: Term, model: Term): Goal =>
    _prop_evalo(fml, PTrue(), model)

  fun _prop_evalo(fml: Term, truth: Term, model: Term): Goal =>
    (symbolo(fml) and asserto(fml, truth, model)) or
    MK.fresh(
      {(fm: Var): Goal =>
        (fml == Formula2(Vl("not"), fm))
        and
          (((truth == Vl("true"))
            and (Propo._prop_evalo(fm, PFalse(), model)))
          or
          ((truth == Vl("false"))
            and (Propo._prop_evalo(fm, PTrue(), model))))
      } val) or
    MK.fresh2(
      {(fm1: Var, fm2: Var): Goal =>
        (fml == Formula3(Vl("->"), fm1, fm2))
        and
          (((truth == Vl("true"))
            and
              ((Propo._prop_evalo(fm1, PTrue(), model) and
                Propo._prop_evalo(fm2, PTrue(), model))
              or
              Propo._prop_evalo(fm1, PFalse(), model)))
          or
          ((truth == Vl("false"))
            and
              ((Propo._prop_evalo(fm1, PTrue(), model) and
                Propo._prop_evalo(fm2, PFalse(), model)))))
      } val) or
    MK.fresh2(
      {(fm1: Var, fm2: Var): Goal =>
        ((fml == Formula3(Vl("^"), fm1, fm2))
          or (fml == Formula3(Vl("and"), fm1, fm2)))
        and
          (((truth == Vl("true"))
            and
              (Propo._prop_evalo(fm1, PTrue(), model) and
                Propo._prop_evalo(fm2, PTrue(), model)))
          or
          ((truth == Vl("false"))
            and
              (Propo._prop_evalo(fm1, PFalse(), model)
                or
                  Propo._prop_evalo(fm2, PFalse(), model))))
      } val) or
    MK.fresh2(
      {(fm1: Var, fm2: Var): Goal =>
        ((fml == Formula3(Vl("v"), fm1, fm2))
          or (fml == Formula3(Vl("or"), fm1, fm2)))
        and
          (((truth == Vl("true"))
            and
              (Propo._prop_evalo(fm1, PTrue(), model) or
                Propo._prop_evalo(fm2, PTrue(), model)))
          or
          ((truth == Vl("false"))
            and
              (Propo._prop_evalo(fm1, PFalse(), model) and
                Propo._prop_evalo(fm2, PFalse(), model))))
      } val)


  // For now, we know this is a symbol if it is a single character
  fun is_symbol(s: String): Bool => s.size() == 1

  fun symbolo(prop: Term): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        (let t: Term, let s': SubstEnv) = MK.walk(prop, sc.subst_env)
        match t
        | let vl: Vl =>
          if Propo.is_symbol(vl.string()) then
            MK.success()(State(s', sc.next_var_id))
          else
            MK.failure()(State(s', sc.next_var_id))
          end
        | let v: Var => MK.success()(State(s', sc.next_var_id))
        else
          MK.failure()(State(s', sc.next_var_id))
        end
    end

// TODO: Use new Pony PEG library to allow Fml to parse more complex
// formula Strings. Currently limited to parsing one level (e.g. "a v b"
// and not "a v (not b)")
class val Fml
  fun apply(s: String): Term =>
    let terms = s.split(" ")
    try
      match terms.size()
      | 1 => Vl(s)
      | 2 => Formula2(Vl(terms(0)), Vl(terms(1)))
      | 3 => Formula3(Vl(terms(1)), Vl(terms(0)), Vl(terms(2)))
      else Vl("invalid-formula-syntax") end
    else Vl("invalid-formula-syntax") end

class val Formula2
  fun apply(op: Vl, fml: Term): Pair =>
    Pair(op, fml)

class val Formula3
  fun apply(op: Vl, fml1: Term, fml2: Term): Pair =>
    Pair(op, Pair(fml1, fml2))

primitive PTrue
  fun apply(): Term => Vl("true")

primitive PFalse
  fun apply(): Term => Vl("false")

primitive Model
  fun apply(ps: Array[String]): Term =>
    if ps.size() == 0 then return TNil() end
    var n = ps.size()
    var m: Term = TNil()
    try
      while n > 0 do
        match model_element(ps(n - 1))
        | let vl: Vl =>
          m = Pair(Pair(vl, PTrue()), m)
        | let p: Pair =>
          m = Pair(p, m)
        end
        n = n - 1
      end
      match m
      | let p: Pair => p
      else
        TNil()
      end
    else
      // This should never happen
      TNil()
    end

  fun model_element(s: String): Term =>
    let components = s.split(" ")
    try
      match components.size()
      | 1 => Vl(s)
      | 2 =>
        if components(0) == "not" then
          Pair(Vl(components(1)), PFalse())
        else
          TNil()
        end
      else TNil() end
    else TNil() end




