actor Main
  new create(env: Env) =>
    @printf[I32]("MicroKanren!\n".cstring())
    run()

  fun run() =>
      @printf[I32]("\nSimple ===\n".cstring())
      let res: Stream[State] =
        MK.call_fresh({(q: Var): Goal => MK.u_u(q, "5")} val)()
      @printf[I32]("%s\n".cstring(), res.string().cstring())
      // Stream((( (#(0) . 5)) . 1))

      @printf[I32]("\nSimple === (where it fails)\n".cstring())
      let v1 = Var(0)
      let state = State(SubstEnv().add(v1, "6"), 1)
      let res01: Stream[State] = MK.u_u(v1, "5")(state)
      @printf[I32]("%s\n".cstring(), res01.string().cstring())
      //Stream()

      @printf[I32]("\nConj\n".cstring())
      let res2 =
        (MK.call_fresh({(q: Var): Goal => MK.u_u(q, "7")} val) and
          MK.call_fresh(
            {(q2: Var): Goal => MK.u_u(q2, "5") or MK.u_u(q2, "6")} val)
        )()
      @printf[I32]("%s\n".cstring(), res2.string().cstring())
      // Stream((( (#(1) . 5) (#(0) . 7)) . 2), (( (#(1) . 6) (#(0) . 7)) . 2))

      @printf[I32]("\nDisj\n".cstring())
      let res3 =
        MK.call_fresh(
          {(q2: Var): Goal =>
            MK.u_u(q2, "5") or MK.u_u(q2, "6")
          } val)()
      @printf[I32]("%s\n".cstring(), res3.string().cstring())
      // Stream((( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1))

      @printf[I32]("\nInfinite (take 20)\n".cstring())
      let res4 = MK.call_fresh(Fives)().take(20)
      @printf[I32]("%s\n".cstring(), res4.string().cstring())
      // Stream((( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1))

      @printf[I32]("\nInifinite (take 20) 2\n".cstring())
      let fives = Repeater("5")
      let sixes = Repeater("6")
      let res5 =
        MK.call_fresh(
          {(q: Var): Goal =>
            fives(q) or sixes(q)
          } val)().take(20)

      @printf[I32]("%s\n".cstring(), res5.string().cstring())
      // Stream((( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1))

      @printf[I32]("\nCheck against disj\n".cstring())
      let res6 =
        MK.call_fresh(
          {(q: Var): Goal =>
            MK.u_u(q, "5") and
            (MK.u_u(q, "6") or MK.u_u(q, "5"))
          } val)()

      @printf[I32]("%s\n".cstring(), res6.string().cstring())
      // Stream((( (#(0) . 5)) . 1))

      @printf[I32]("\nConso\n".cstring())
      let res7 =
        MK.call_fresh(
          {(q: Var): Goal =>
            MK.conso("a", TList("b c"), q)
          } val)()

      @printf[I32]("%s\n".cstring(), res7.string().cstring())
      // Stream((( (#(0) . (a . (b . (c . ))))) . 1))

      @printf[I32]("\nConso2\n".cstring())
      let res8 =
        MK.call_fresh(
          {(q: Var): Goal =>
            MK.conso(q, TList("b c d"), TList("a b c d"))
          } val)()

      @printf[I32]("%s\n".cstring(), res8.string().cstring())
      // Stream((( (#(0) . a)) . 1))

      @printf[I32]("\nConso3\n".cstring())
      let res9 =
        MK.fresh3(
          {(q1: Var, q2: Var, q3: Var): Goal =>
            MK.conso(q1, q2, q3)
          } val)()

      @printf[I32]("%s\n".cstring(), res9.string().cstring())
      // Stream((( (#(2) . (#(0) . #(1)))) . 3))

      @printf[I32]("\nRelation\n".cstring())
      let res10 =
        MK.call_fresh(
          {(q: Var): Goal =>
            LocatedIn("Bronx", q)
          } val)().take(10)

      @printf[I32]("%s\n".cstring(), res10.string().cstring())
      // Stream((( (#(0) . NY)) . 3), (( (#(1) . NY) (#(0) . US)) . 5), (( (#(1) . NY) (#(0) . Earth) (#(3) . US)) . 7))
      @printf[I32]("Reified: %s\n".cstring(),
        MK.reify_items(res10).string().cstring())
      // Reified: Stream(NY, US, Earth)

      @printf[I32]("\nRelation2\n".cstring())
      let res11 =
        MK.call_fresh(
          {(q: Var): Goal =>
            LocatedIn(q, "Earth")
          } val)().take(10)

      @printf[I32]("%s\n".cstring(), res11.string().cstring())
      // Stream((( (#(0) . WA)) . 3), (( (#(0) . NY)) . 3), (( (#(1) . NY) (#(0) . Bronx)) . 5), (( (#(1) . WA) (#(0) . Seattle)) . 5))
      @printf[I32]("Reified: %s\n".cstring(),
        MK.reify_items(res11).string().cstring())
      // Reified: Stream(WA, NY, Bronx, Seattle)

      @printf[I32]("\nAppendo\n".cstring())
      let res12 =
        MK.call_fresh(
          {(q1: Var): Goal =>
            MK.appendo(TList("a b"), TList("c d"), q1)
          } val)()

      @printf[I32]("%s\n".cstring(), res12.string().cstring())
      @printf[I32]("Reified: %s\n".cstring(),
        MK.reify(res12).string().cstring())

      @printf[I32]("\nAppendo\n".cstring())
      let res13 =
        MK.fresh2(
          {(q1: Var, q2: Var): Goal =>
            MK.appendo(q1, q2, TList("a b c d e"))
          } val)()

      @printf[I32]("%s\n".cstring(), res13.string().cstring())
      @printf[I32]("%lu\n".cstring(), res13.size())
      @printf[I32]("Reified: %s\n".cstring(),
        MK.reify2(res13).string().cstring())

      @printf[I32]("\nMembero\n".cstring())
      let res14 =
        MK.call_fresh(
          {(q1: Var): Goal =>
            MK.membero("a", q1)
          } val)().take(10)

      @printf[I32]("%s\n".cstring(), res14.string().cstring())
      @printf[I32]("Reified: %s\n".cstring(),
        MK.reify(res14).string().cstring())

      @printf[I32]("\nMatch_listo1\n".cstring())
      let res15 =
        MK.call_fresh(
          {(q1: Var): Goal =>
            MK.match_listo(TList("a b c d e"), q1)
          } val)()

      @printf[I32]("Reified: %s\n".cstring(),
        MK.reify(res15).string().cstring())


      @printf[I32]("\nMatch_listo2\n".cstring())
      let res16 =
          MK.match_listo(TList("a _ c _ e"), TList("a b c d e"))()

      @printf[I32]("Reified: %s\n".cstring(),
        MK.reify(res16).string().cstring())

primitive LocatedIn
  fun apply(t1: Term, t2: Term): Goal =>
    TransitiveRelation(recover [
      ("Bronx", "NY")
      ("Seattle", "WA")
      ("WA", "US")
      ("NY", "US")
      ("US", "Earth")
      ("Earth", "Cosmos")
    ] end)(t1, t2)

primitive Fives
  fun apply(x: Var): Goal =>
    MK.u_u(x, "5") or
      object val is Goal
        let x: Var = x
        fun apply(sc: State): Stream[State] =>
          SDelay[State]({(): Stream[State] => Fives.apply(x)(sc)} val)
      end

class val Repeater
  let _v: String

  new val create(v: String) =>
    _v = v

  fun val apply(x: Var): Goal =>
    MK.u_u(x, _v) or
      object val is Goal
        let x: Var = x
        let self: Repeater = this
        fun apply(sc: State): Stream[State] =>
          SDelay[State]({(): Stream[State] => self(x)(sc)} val)
      end

primitive Helpers
  fun righto(t1: Term, t2: Term, lst: Term): Goal =>
    MK.fresh3(
      {(h: Var, tail1: Var, tail2: Var): Goal =>
        (MK.conso(t1, tail1, lst) and
          MK.conso(t2, tail2, tail1)) or
        (MK.conso(h, tail1, lst) and
          Helpers.righto(t1, t2, tail1))
      } val)

  fun nexto(t1: Term, t2: Term, lst: Term): Goal =>
    righto(t1, t2, lst) or righto(t2, t1, lst)

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

