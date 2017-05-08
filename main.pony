actor Main
  new create(env: Env) =>
    @printf[I32]("pony-logic!\n".cstring())
    run()

  fun run() =>
      @printf[I32]("\nSimple ===\n".cstring())
      let res: Stream[State] =
        MK.fresh({(q: Var): Goal => q == Vl("5")} val)()
      @printf[I32]("%s\n".cstring(), res.string().cstring())
      // Stream((( (#(0) . 5)) . 1))

      @printf[I32]("\nSimple === (where it fails)\n".cstring())
      let v1 = Var(0)
      let state = State(SubstEnv().add(v1, Vl("6")), 1)
      let res01: Stream[State] = (v1 == Vl("5"))(state)
      @printf[I32]("%s\n".cstring(), res01.string().cstring())
      //Stream()

      @printf[I32]("\nConj\n".cstring())
      let res2 =
        (MK.fresh({(q: Var): Goal => (q == Vl("7"))} val) and
          MK.fresh(
            {(q2: Var): Goal => (q2 == Vl("5")) or (q2 == Vl("6"))} val)
        )()
      @printf[I32]("%s\n".cstring(), res2.string().cstring())
      // Stream((( (#(1) . 5) (#(0) . 7)) . 2), (( (#(1) . 6) (#(0) . 7)) . 2))

      @printf[I32]("\nDisj\n".cstring())
      let res3 =
        MK.fresh(
          {(q2: Var): Goal =>
            (q2 == Vl("5")) or (q2 == Vl("6"))
          } val)()
      @printf[I32]("%s\n".cstring(), res3.string().cstring())
      // Stream((( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1))

      @printf[I32]("\nInfinite (take 20)\n".cstring())
      let res4 = MK.fresh(Fives)().take(20)
      @printf[I32]("%s\n".cstring(), res4.string().cstring())
      // Stream((( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 5)) . 1))

      @printf[I32]("\nInifinite (take 20) 2\n".cstring())
      let fives = Repeater(Vl("5"))
      let sixes = Repeater(Vl("6"))
      let res5 =
        MK.fresh(
          {(q: Var): Goal =>
            fives(q) or sixes(q)
          } val)().take(20)

      @printf[I32]("%s\n".cstring(), res5.string().cstring())
      // Stream((( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1), (( (#(0) . 5)) . 1), (( (#(0) . 6)) . 1))

      @printf[I32]("\nCheck against disj\n".cstring())
      let res6 =
        MK.fresh(
          {(q: Var): Goal =>
            (q == Vl("5")) and
            ((q == Vl("6")) or (q == Vl("5")))
          } val)()

      @printf[I32]("%s\n".cstring(), res6.string().cstring())
      // Stream((( (#(0) . 5)) . 1))

      @printf[I32]("\nConso\n".cstring())
      let res7 =
        MK.fresh(
          {(q: Var): Goal =>
            MK.conso(Vl("a"), TList("b c"), q)
          } val)()

      @printf[I32]("%s\n".cstring(), res7.string().cstring())
      // Stream((( (#(0) . (a . (b . (c . ))))) . 1))

      @printf[I32]("\nConso2\n".cstring())
      let res8 =
        MK.fresh(
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
        MK.fresh(
          {(q: Var): Goal =>
            LocatedIn(Vl("Bronx"), q)
          } val)().take(10)

      @printf[I32]("%s\n".cstring(), res10.string().cstring())
      @printf[I32]("Reified: %s\n".cstring(),
        MK.reify_items(res10).string().cstring())
      // Reified: Stream(NY, US, Earth, Cosmos)

      @printf[I32]("\nRelation2\n".cstring())
      let res11 =
        MK.fresh(
          {(q: Var): Goal =>
            LocatedIn(q, Vl("Earth"))
          } val)().take(10)

      @printf[I32]("%s\n".cstring(), res11.string().cstring())
      // Stream((( (#(0) . WA)) . 3), (( (#(0) . NY)) . 3), (( (#(1) . NY) (#(0) . Bronx)) . 5), (( (#(1) . WA) (#(0) . Seattle)) . 5))
      @printf[I32]("Reified: %s\n".cstring(),
        MK.reify_items(res11).string().cstring())
      // Reified: Stream(WA, NY, Bronx, Seattle)


      @printf[I32]("\nDivergo (printing this result would diverge)\n"
        .cstring())
      let res666 =
        MK.fresh2(
          {(q1: Var, q2: Var): Goal =>
            MK.divergo()
          } val)()

      @printf[I32]("\nAppendo1\n".cstring())
      let res12 =
        MK.fresh(
          {(q1: Var): Goal =>
            MK.appendo(TList("a b"), TList("c d"), q1)
          } val)()

      @printf[I32]("Reified: %s\n".cstring(),
        MK.reify(res12).string().cstring())
      // Reified: Stream(
      // [0: (a . (b . (c . (d . ()))))])

      @printf[I32]("\nAppendo2\n".cstring())
      let res13 =
        MK.fresh2(
          {(q1: Var, q2: Var): Goal =>
            MK.appendo(q1, q2, TList("a b c d e"))
          } val)().take(10)

      @printf[I32]("Reified: %s\n".cstring(),
        MK.reify2(res13).string().cstring())
      // Reified: Stream(
      // [0: (), 1: (a . (b . (c . (d . (e . ())))))],
      // [0: (a . ()), 1: (b . (c . (d . (e . ()))))],
      // [0: (a . (b . ())), 1: (c . (d . (e . ())))],
      // [0: (a . (b . (c . ()))), 1: (d . (e . ()))],
      // [0: (a . (b . (c . (d . ())))), 1: (e . ())],
      // [0: (a . (b . (c . (d . (e . ()))))), 1: ()])

      @printf[I32]("\nAppendo3\n".cstring())
      let res14 =
        MK.fresh2(
          {(q1: Var, q2: Var): Goal =>
            MK.appendo(q1, TList("d e"), q2)
          } val)().take(10)

      @printf[I32]("Reified: %s\n".cstring(),
        MK.reify2(res14).string().cstring())

      @printf[I32]("\nMembero\n".cstring())
      let res15 =
        MK.fresh(
          {(q1: Var): Goal =>
            MK.membero(Vl("a"), q1)
          } val)().take(10)

      @printf[I32]("Reified: %s\n".cstring(),
        MK.reify(res15).string().cstring())
      // Reified: Stream(
      // [0: (a . #(1))],
      // [0: (#(2) . (a . #(3)))],
      // [0: (#(2) . (#(4) . (a . #(5))))],
      // [0: (#(2) . (#(4) . (#(6) . (a . #(7)))))],
      // [0: (#(2) . (#(4) . (#(6) . (#(8) . (a . #(9))))))],
      // [0: (#(2) . (#(4) . (#(6) . (#(8) . (#(10) . (a . #(11)))))))],
      // [0: (#(2) . (#(4) . (#(6) . (#(8) . (#(10) . (#(12) . (a . #(13))))))))],
      // [0: (#(2) . (#(4) . (#(6) . (#(8) . (#(10) . (#(12) . (#(14) . (a . #(15)))))))))],
      // [0: (#(2) . (#(4) . (#(6) . (#(8) . (#(10) . (#(12) . (#(14) . (#(16) . (a . #(17))))))))))],
      // [0: (#(2) . (#(4) . (#(6) . (#(8) . (#(10) . (#(12) . (#(14) . (#(16) . (#(18) . (a . #(19)))))))))))])

      @printf[I32]("\nPattern\n".cstring())
      let res16 =
        MK.fresh(
          {(q1: Var): Goal =>
            (q1 == TList("_ w _")) and (q1 == TList("b _ _"))
              and (q1 == TList("_ _ c"))
          } val)().take(10)

      @printf[I32]("Reified: %s\n".cstring(),
        MK.reify(res16).string().cstring())
      // Reified: Stream(
      // [0: (b . (w . (c . ())))])

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
    (x == Vl("5")) or
      object val is Goal
        let x: Var = x
        fun apply(sc: State): Stream[State] =>
          SDelay[State]({(): Stream[State] => Fives.apply(x)(sc)} val)
      end

class val Repeater
  let _v: Vl

  new val create(v: Vl) =>
    _v = v

  fun val apply(x: Var): Goal =>
    (x == _v) or
      object val is Goal
        let x: Var = x
        let self: Repeater = this
        fun apply(sc: State): Stream[State] =>
          SDelay[State]({(): Stream[State] => self(x)(sc)} val)
      end

primitive Helpers
  fun righto(t1: Term, t2: Term, lst: Term): Goal =>
    MK.fresh(
      {(tail: Var): Goal =>
          (MK.conso(t1, tail, lst) and
          MK.heado(t2, tail)) or
        MK.delay(
          MK.conso(PAny, tail, lst) and
          MK.delay((Helpers.righto(t1, t2, tail))))
      } val)

  fun nexto(t1: Term, t2: Term, lst: Term): Goal =>
    righto(t1, t2, lst) or righto(t2, t1, lst)

primitive TList2
  fun apply(arr: Array[String]): Term =>
    var n = arr.size()
    if n == 0 then return TNil() end
    var l: Term = TNil()
    try
      while n > 0 do
        let next: (PAny | String) =
          match arr(n - 1)
          | "_" => PAny
          | let s: String => s
          else arr(n - 1) end
        match next
        | let p: PAny =>
          l = Pair(p, l)
        | let s: String =>
          l = Pair(TList(s), l)
        end
        n = n - 1
      end

      match l
      | let p: Pair =>
        var is_pattern = false
        for s in arr.values() do
          if s.contains("_") then is_pattern = true end
        end
        if is_pattern then PList(p) else p end
      else
        TNil()
      end
    else
      // This should never happen
      TNil()
    end

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

