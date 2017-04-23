actor Main
  new create(env: Env) =>
    @printf[I32]("MicroKanren!\n".cstring())
    run()

  fun run() =>
    // try
      // @printf[I32]("Ones:\n".cstring())
      // let ones = Ones
      // let first_ten = ones.take(1000)
      // @printf[I32]("%s\n".cstring(), first_ten.string().cstring())

      // @printf[I32]("\nNaturals:\n".cstring())
      // let natural = U8s
      // let first_ten_nats = natural.take(10).reverse()
      // @printf[I32]("%s\n".cstring(), first_ten_nats.string().cstring())

      // @printf[I32]("\nMerged Evens and Odds:\n".cstring())
      // let merge = SMerge[U8](Evens, Odds)
      // let first_ten_merged = merge.take(20).reverse()
      // @printf[I32]("%s\n".cstring(), first_ten_merged.string().cstring())

      // @printf[I32]("\nMerge/filter/map:\n".cstring())
      // let merge =
      //   Streams[U8].map[String]({(u: U8): String => (u * 2).string()},
      //     Evens.merge(Odds).filter({(u: U8): Bool => (u % 3) == 0}).take(50))
      // let first_ten_merge_filter_map = merge.take(50)
      // @printf[I32]("%s\n".cstring(), first_ten_merge_filter_map.string()
      //   .cstring())

      @printf[I32]("Unify\n".cstring())
      let mk = MK
      let res: Stream[State val] val =
        MK.call_fresh(
          recover
            {
              (q: Var val)(mk): Goal val => mk.u_u(q, "5")
            }
          end)(mk.empty_state())
      @printf[I32]("%s\n".cstring(), res.string().cstring())

      @printf[I32]("Unify2\n".cstring())
      let v1 = Var(0)
      let state = State(SubstEnv().add(v1, "6"), 1)
      let res01: Stream[State val] val =
        mk.u_u(v1, "5")(state)
      @printf[I32]("%s\n".cstring(), res01.string().cstring())

      @printf[I32]("Conj\n".cstring())
      let res2 =
        MK.conj(
          MK.call_fresh(
            recover
              {
                (q: Var val)(mk): Goal val => mk.u_u(q, "7")
              }
            end),
          MK.call_fresh(
            recover
              {
                (q2: Var val)(mk): Goal val => mk.disj(
                  mk.u_u(q2, "5"),
                  mk.u_u(q2, "6"))
              }
            end))(mk.empty_state())
      @printf[I32]("%s\n".cstring(), res2.string().cstring())
      @printf[I32]("%lu\n".cstring(), res2.size())

      @printf[I32]("Disj\n".cstring())
      let res3 =
        MK.call_fresh(
          recover
            {
              (q2: Var val)(mk): Goal val => mk.disj(
                mk.u_u(q2, "5"),
                mk.u_u(q2, "6"))
            }
          end)(mk.empty_state())
      @printf[I32]("%s\n".cstring(), res3.string().cstring())
      @printf[I32]("%lu\n".cstring(), res3.size())

      @printf[I32]("Infinite\n".cstring())
      let res4 =
        MK.call_fresh(Fives)(mk.empty_state()).take(20)
      @printf[I32]("%s\n".cstring(), res4.string().cstring())
      @printf[I32]("%lu\n".cstring(), res4.size())

      let fives = Repeater("5")
      let sixes = Repeater("6")
      let res5 =
        MK.call_fresh(
          recover
            {
              (q: Var val)(fives, sixes): Goal val => mk.disj(
                fives(q),
                sixes(q))
            }
          end)(mk.empty_state()).take(20)

      @printf[I32]("%s\n".cstring(), res5.string().cstring())
      @printf[I32]("%lu\n".cstring(), res5.size())

      @printf[I32]("Find\n".cstring())
      let res6 =
        MK.call_fresh(
          recover
            {
              (q: Var val)(mk): Goal val => mk.conj(
                mk.u_u(q, "5"),
                mk.disj(
                  mk.u_u(q, "6"),
                  mk.u_u(q, "5")
                ))
            }
          end)(mk.empty_state())

      @printf[I32]("%s\n".cstring(), res6.string().cstring())
      @printf[I32]("%lu\n".cstring(), res6.size())

      @printf[I32]("Conso\n".cstring())
      let res7 =
        MK.call_fresh(
          recover
            {
              (q: Var val)(mk): Goal val =>
                mk.conso("a", TList("b c"), q)
            }
          end)(mk.empty_state())

      @printf[I32]("%s\n".cstring(), res7.string().cstring())

      @printf[I32]("Conso2\n".cstring())
      let res8 =
        MK.call_fresh(
          recover
            {
              (q: Var val)(mk): Goal val =>
                mk.conso(q, TList("b c d"), TList("a b c d"))
            }
          end)(mk.empty_state())

      @printf[I32]("%s\n".cstring(), res8.string().cstring())

      @printf[I32]("Conso3\n".cstring())
      let res9 =
        MK.call_fresh(
          recover
            {
              (q1: Var val)(mk): Goal val => mk.call_fresh(
                recover {
                  (q2: Var val)(mk, q1): Goal val => mk.call_fresh(
                    recover {
                      (q3: Var val)(mk, q1, q2): Goal val =>
                        mk.conso(q1, q2, q3)
                    } end)
                } end)
            }
          end)(mk.empty_state())

      @printf[I32]("%s\n".cstring(), res9.string().cstring())

    // else
    //   @printf[I32]("Something went wrong!\n".cstring())
    // end

primitive Fives
  fun apply(x: Var val): Goal val =>
    let fives = Fives
    MK.disj(
      MK.u_u(x, "5"),
      recover
        {(sc: State val)(x, fives): Stream[State val] val =>
          SDelay[State val](recover
            {()(fives): Stream[State val] val => fives.apply(x)(sc)}
          end)
        }
      end
    )

class Repeater
  let _v: String

  new val create(v: String) =>
    _v = v

  fun apply(x: Var val): Goal val =>
    let r = Repeater(_v)
    MK.disj(
      MK.u_u(x, _v),
      recover
        {(sc: State val)(x, r): Stream[State val] val =>
          SDelay[State val](recover
            {()(r): Stream[State val] val => r.apply(x)(sc)}
          end)
        }
      end
    )

//////////////////////////
// Some infinite streams
//////////////////////////
primitive Ones is SNext[U8]
  fun mature(): (U8, Stream[U8] val) =>
    (1, Ones)

class U8s is SNext[U8]
  let _n: U8

  new val create(n: U8 = 0) =>
    _n = n

  fun mature(): (U8, Stream[U8] val) =>
    if _n == U8.max_value() then
      (_n, SNil[U8])
    else
      (_n, U8s(_n + 1))
    end

class Odds is SNext[U8]
  let _n: U8

  new val create(n: U8 = 1) =>
    _n =
      if (n % 2) == 0 then
        n + 1
      else
        n
      end

  fun mature(): (U8, Stream[U8] val) =>
    if _n == U8.max_value() then
      (_n, SNil[U8])
    else
      (_n, Odds(_n + 2))
    end

class Evens is SNext[U8]
  let _n: U8

  new val create(n: U8 = 0) =>
    _n =
      if (n % 2) != 0 then
        n + 1
      else
        n
      end

  fun mature(): (U8, Stream[U8] val) =>
    if _n == U8.max_value() then
      (_n, SNil[U8])
    else
      (_n, Evens(_n + 2))
    end

