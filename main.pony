actor Main
  new create(env: Env) =>
    @printf[I32]("MicroKanren!\n".cstring())
    run()

  fun run() =>
      @printf[I32]("\nSimple ===\n".cstring())
      let res: Stream[State] =
        MK.call_fresh({(q: Var): Goal => MK.u_u(q, "5")} val)(MK.empty_state())
      @printf[I32]("%s\n".cstring(), res.string().cstring())
      // Stream((( (#(0) . 5)) . 1))

      @printf[I32]("\nSimple === (where it fails)\n".cstring())
      let v1 = Var(0)
      let state = State(SubstEnv().add(v1, "6"), 1)
      let res01: Stream[State] = MK.u_u(v1, "5")(state)
      @printf[I32]("%s\n".cstring(), res01.string().cstring())
      // Stream()

      @printf[I32]("\nConj\n".cstring())
      let res2 =
        MK.conj(
          MK.call_fresh({(q: Var): Goal => MK.u_u(q, "7")} val),
          MK.call_fresh({(q2: Var): Goal => MK.disj(
            MK.u_u(q2, "5"),
            MK.u_u(q2, "6"))} val)
          )(MK.empty_state())
      @printf[I32]("%s\n".cstring(), res2.string().cstring())
      // Stream((( (#(1) . 5) (#(0) . 7)) . 2), (( (#(1) . 6) (#(0) . 7)) . 2))

      @printf[I32]("\nDisj\n".cstring())
      let res3 =
        MK.call_fresh({(q2: Var): Goal => MK.disj(
          MK.u_u(q2, "5"),
          MK.u_u(q2, "6"))} val
        )(MK.empty_state())
      @printf[I32]("%s\n".cstring(), res3.string().cstring())
      // Stream((( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1))

      @printf[I32]("\nInfinite (take 20)\n".cstring())
      let res4 = MK.call_fresh(Fives)(MK.empty_state()).take(20)
      @printf[I32]("%s\n".cstring(), res4.string().cstring())
      // Stream((( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1))

      @printf[I32]("\nInifinite (take 20) 2\n".cstring())
      let fives = Repeater("5")
      let sixes = Repeater("6")
      let res5 =
        MK.call_fresh({(q: Var)(fives, sixes): Goal => MK.disj(
          fives(q),
          sixes(q))} val
        )(MK.empty_state()).take(20)

      @printf[I32]("%s\n".cstring(), res5.string().cstring())
      // Stream((( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1))

      @printf[I32]("\nCheck against disj\n".cstring())
      let res6 =
        MK.call_fresh({(q: Var): Goal => MK.conj(
          MK.u_u(q, "5"),
          MK.disj(
            MK.u_u(q, "6"),
            MK.u_u(q, "5")
          ))} val
        )(MK.empty_state())

      @printf[I32]("%s\n".cstring(), res6.string().cstring())
      // Stream((( (#(0) . 5)) . 1))

      @printf[I32]("\nConso\n".cstring())
      let res7 =
        MK.call_fresh({(q: Var): Goal =>
          MK.conso("a", TList("b c"), q)} val
        )(MK.empty_state())

      @printf[I32]("%s\n".cstring(), res7.string().cstring())
      // Stream((( (#(0) . (a . (b . (c . ))))) . 1))

      @printf[I32]("\nConso2\n".cstring())
      let res8 =
        MK.call_fresh({(q: Var): Goal =>
          MK.conso(q, TList("b c d"), TList("a b c d"))} val
        )(MK.empty_state())

      @printf[I32]("%s\n".cstring(), res8.string().cstring())
      // Stream((( (#(0) . a)) . 1))

      @printf[I32]("\nConso3\n".cstring())
      let res9 =
        MK.fresh3({(q1: Var, q2: Var, q3: Var): Goal =>
          MK.conso(q1, q2, q3)} val
        )(MK.empty_state())

      @printf[I32]("%s\n".cstring(), res9.string().cstring())
      // Stream((( (#(2) . (#(0) . #(1)))) . 3))

      @printf[I32]("\nRelation\n".cstring())
      let res10 =
        MK.call_fresh({(q: Var): Goal =>
          Relations.located_in("Bronx", q)} val
        )(MK.empty_state()).take(10)

      @printf[I32]("%s\n".cstring(), res10.string().cstring())
      // Stream((( (#(0) . NY)) . 3), (( (#(1) . NY) (#(0) . US)) . 3))

      @printf[I32]("\nRelation2\n".cstring())
      let res11 =
        MK.call_fresh({(q: Var): Goal =>
          Relations.located_in(q, "US")}
        )(MK.empty_state()).take(10)

      @printf[I32]("%s\n".cstring(), res11.string().cstring())
      // Stream((( (#(0) . WA)) . 3), (( (#(0) . NY)) . 3), (( (#(1) . NY) (#(0) . Bronx)) . 3), (( (#(1) . WA) (#(0) . Seattle)) . 3))

primitive Relations
  fun _located_in(t1: Term, t2: Term): Goal =>
    MK.conde([
      [MK.u_u("Bronx", t1); MK.u_u("NY", t2)]
      [MK.u_u("Seattle", t1); MK.u_u("WA", t2)]
      [MK.u_u("WA", t1); MK.u_u("US", t2)]
      [MK.u_u("NY", t1); MK.u_u("US", t2)]
      [MK.u_u("US", t1); MK.u_u("Earth", t2)]
    ])

  fun located_in(t1: Term, t2: Term): Goal =>
    let relations = Relations
    MK.fresh2({(q1: Var, q2: Var)(relations): Goal =>
      MK.conde([
        [relations._located_in(t1, t2)]
        [relations._located_in(t1, q1); relations._located_in(q1, t2)]
      ])} val
    )

primitive Fives
  fun apply(x: Var): Goal =>
    let fives = Fives
    MK.disj(
      MK.u_u(x, "5"),
        {(sc: State)(x, fives): Stream[State] =>
          SDelay[State](recover
            {()(fives): Stream[State] => fives.apply(x)(sc)}
          end)} val)

class Repeater
  let _v: String

  new val create(v: String) =>
    _v = v

  fun apply(x: Var): Goal =>
    let r = Repeater(_v)
    MK.disj(
      MK.u_u(x, _v),
        {(sc: State)(x, r): Stream[State] =>
          SDelay[State]({()(r): Stream[State] => r.apply(x)(sc)} val)
        } val)

//////////////////////////
// Some infinite streams
//////////////////////////
primitive Ones is SNext[U8]
  fun mature(): (U8, Stream[U8]) =>
    (1, Ones)

class val U8s is SNext[U8]
  let _n: U8

  new val create(n: U8 = 0) =>
    _n = n

  fun mature(): (U8, Stream[U8]) =>
    if _n == U8.max_value() then
      (_n, SNil[U8])
    else
      (_n, U8s(_n + 1))
    end

class val Odds is SNext[U8]
  let _n: U8

  new val create(n: U8 = 1) =>
    _n =
      if (n % 2) == 0 then
        n + 1
      else
        n
      end

  fun mature(): (U8, Stream[U8]) =>
    if _n == U8.max_value() then
      (_n, SNil[U8])
    else
      (_n, Odds(_n + 2))
    end

class val Evens is SNext[U8]
  let _n: U8

  new val create(n: U8 = 0) =>
    _n =
      if (n % 2) != 0 then
        n + 1
      else
        n
      end

  fun mature(): (U8, Stream[U8]) =>
    if _n == U8.max_value() then
      (_n, SNil[U8])
    else
      (_n, Evens(_n + 2))
    end

