
interface Printable
  fun string(): String


type Stream[A: Any val] is (SCons[A] | SNext[A] | SNil[A])

primitive SNil[A: Any val]
  """
  The empty stream of As.
  """

  fun mature(): (A, Stream[A]) ? =>
    error

  fun val force(): Stream[A] val =>
    this

  fun size(): USize =>
    """
    It's unwise to call size() on an infinite stream
    """
    0

  fun is_empty(): Bool =>
    """
    Returns a Bool indicating if the stream is empty.
    """
    true

  fun is_non_empty(): Bool =>
    """
    Returns a Bool indicating if the stream is non-empty.
    """
    false

  fun head(): val->A ? =>
    """
    Returns an error, since Nil has no head.
    """
    error

  fun tail(): Stream[A] ? =>
    """
    Returns an error, since Nil has no tail.
    """
    error

  fun val map[B: Any val](f: {(A): B} val): Stream[B] val =>
    SNil[B]

  fun val flat_map[B: Any val](f: {(A): Stream[B] val} val): Stream[B] val =>
    SNil[B]

  fun val filter(pred: {(A): Bool} val): Stream[A] val =>
    SNil[A]

  fun val merge(s2: Stream[A] val): Stream[A] val =>
    s2

  fun val delay(): Stream[A] val =>
    SNil[A]

  fun val reverse(): SNil[A] =>
    """
    Builds a new stream by reversing the elements in the stream.
    """
    this

  fun val prepend(a: val->A): SCons[A] =>
    SCons[A](a, this)

  fun take(n: USize): SNil[A] =>
    """
    There are no elements to take from the empty stream.
    """
    this

  fun string(): String =>
    "Stream()"

  fun _string(): String =>
    ")"

trait val SNext[A: Any val]
  // In order to implement an SNext, you only need an implementation
  // of mature()
  fun mature(): (A, Stream[A]) ?

  fun val force(): Stream[A] val =>
    try
      // This weird line is because the compiler doesn't see the mature()
      // line as possibly raising an error when wrapped in a try block
      // TODO: Address and remove
      if false then error end

      (let h: A, let t: Stream[A] val) = mature()
      SCons[A](h, t)
    else
      SNil[A]
    end

  fun val size(): USize =>
    """
    It's unwise to call size() on an infinite stream
    """
    force().size()

  fun is_empty(): Bool =>
    """
    Returns a Bool indicating if the stream is empty.
    """
    false

  fun is_non_empty(): Bool =>
    """
    Returns a Bool indicating if the stream is non-empty.
    """
    true

  fun head(): val->A ? =>
    """
    Returns the head of the stream.
    """
    mature()._1

  fun tail(): Stream[A] ? =>
    """
    Returns the tail of the stream.
    """
    mature()._2

  // TODO: Determine why compiler refuses to accept this use of
  // type parameter B: Any val on SNext (but not SCons) for map and
  // flat_map.
  // fun val map[B: Any val](f: {(A): B} val): SMap[A, B] val =>
  //   match force()
  //   | let cons: SCons[A] val => cons.map[B](f)
  //   else
  //     SNil[A].map[B](f)
  //   end

  // fun val flat_map[B: Any val](f: {(A): Stream[B] val} val):
  //   SFlatMap[A, B] val
  // =>
  //   force().flat_map[B](f)

  fun val filter(pred: {(A): Bool} val): Stream[A] val =>
    SFilter[A](pred, this)

  fun val merge(s2: Stream[A] val): Stream[A] val =>
    SMerge[A](this, s2)

  fun val delay(): Stream[A] val =>
    force().delay()
    //TODO: Determine why compiler thinks self is not of type Stream[A] and
    // replace the force() line with these:
    // let self = this
    // SDelay[A](recover {()(self): Stream[A] val => self} end)

  fun val reverse(): Stream[A] =>
    """
    Builds a new stream by reversing the elements in the stream.
    """
    Streams[A].reverse(this)

  fun val prepend(a: val->A): SCons[A] =>
    """
    Builds a new stream with an element added to the front of this stream.
    """
    SCons[A](a, this)

  fun val take(n: USize): Stream[A] =>
    """
    Builds a stream of the first n elements.
    """
    Streams[A].take(n, this)

  fun string(): String =>
    try
      match head()
      | let str: Printable val =>
        try
          "Stream(" + str.string() + tail()._string()
        else
          "Stream(" + str.string() + ")"
        end
      else
        try
          "Stream(" + "?" + tail()._string()
        else
          "Stream(" + "?" + ")"
        end
      end
    else
      "Stream()"
    end

  fun _string(): String =>
    try
      match head()
      | let str: Printable val =>
        try
          ", " + str.string() + tail()._string()
        else
          ", " + str.string() + ")"
        end
      else
        try
          ", " + "?" + tail()._string()
        else
          ", " + "?" + ")"
        end
      end
    else
      "Stream()"
    end

class val SCons[A: Any val]
  """
  A stream with a head and a tail, where the tail can be empty.
  """

  let _head: A
  let _tail: Stream[A] val

  new val create(h: A, t: Stream[A] val) =>
    _head = h
    _tail = t

  fun mature(): (A, Stream[A] val) =>
    (_head, _tail)

  fun val force(): Stream[A] val =>
    this

  fun size(): USize =>
    """
    It's unwise to call size() on an infinite stream
    """
    1 + _tail.size()

  fun is_empty(): Bool =>
    """
    Returns a Bool indicating if the stream is empty.
    """
    false

  fun is_non_empty(): Bool =>
    """
    Returns a Bool indicating if the stream is non-empty.
    """
    true

  fun head(): val->A =>
    """
    Returns the head of the stream.
    """
    _head

  fun tail(): Stream[A] =>
    """
    Returns the tail of the stream.
    """
    _tail

  fun val map[B: Any val](f: {(A): B} val): Stream[B] val =>
    SMap[A, B](f, this)

  fun val flat_map[B: Any val](f: {(A): Stream[B] val} val): Stream[B] val =>
    SFlatMap[A, B](f, this)

  fun val filter(pred: {(A): Bool} val): Stream[A] val =>
    SFilter[A](pred, this)

  fun val merge(s2: Stream[A] val): Stream[A] val =>
    SMerge[A](this, s2)

  fun val delay(): Stream[A] val =>
    let self = this
    SDelay[A](recover {()(self): Stream[A] val => self} end)

  fun val reverse(): Stream[A] =>
    """
    Builds a new stream by reversing the elements in the stream.
    """
    Streams[A].reverse(this)

  fun val prepend(a: val->A): SCons[A] =>
    """
    Builds a new stream with an element added to the front of this stream.
    """
    SCons[A](a, this)

  fun val take(n: USize): Stream[A] =>
    """
    Builds a stream of the first n elements.
    """
    Streams[A].take(n, this)

  fun string(): String =>
    match head()
    | let str: Printable val =>
      "Stream(" + str.string() + tail()._string()
    else
      "Stream(" + "?" + tail()._string()
    end

  fun _string(): String =>
    match head()
    | let str: Printable val =>
      ", " + str.string() + tail()._string()
    else
      ", " + "?" + tail()._string()
    end

primitive Streams[A: Any val]
  fun val reverse(l: Stream[A]): Stream[A] =>
    _reverse(l, SNil[A])

  fun val _reverse(l: Stream[A], acc: Stream[A]): Stream[A] =>
    """
    Private helper for reverse, recursively working on elements.
    """
    match l.force()
    | let cons: SCons[A] val => _reverse(cons.tail(), acc.prepend(cons.head()))
    else
      acc
    end

  fun val take(n: USize, s: Stream[A]): Stream[A] =>
    """
    Builds a stream of the first n elements.
    """
    var cur: Stream[A] = s
    var count = n
    var res: Stream[A] = SNil[A]
    while(count > 0) do
      match cur.force()
      | let cons: SCons[A] val =>
        res = res.prepend(cons.head())
        cur = cons.tail()
      else
        return res.reverse()
      end
      count = count - 1
    end
    res.reverse()

  // TODO: Remove this once compiler type issues are resolved above for SNext
  fun val map[B: Any val](f: {(A): B} val, s: Stream[A] val): Stream[B] val =>
    SMap[A, B](f, s)

  // TODO: Remove this once compiler type issues are resolved above for SNext
  fun val flat_map[B: Any val](f: {(A): Stream[B] val} val, s: Stream[A] val):
    Stream[B] val
  =>
    SFlatMap[A, B](f, s)

//////////////////////////
// SNext implementations
//////////////////////////
class SMerge[A: Any val] is SNext[A]
  """
  Interleave two streams
  """
  let _l: Stream[A] val
  let _r: Stream[A] val

  new val create(l: Stream[A] val, r: Stream[A] val) =>
    _l = l
    _r = r

  fun mature(): (A, Stream[A] val) ? =>
    match (_l, _r)
    | (let l: SNil[A] val, _) => _r.mature()
    | (_, let r: SNil[A] val) => _l.mature()
    else
      (let h: A, let t: Stream[A] val) = _l.mature()
      (h, SMerge[A](_r, t))
    end

class SDelay[A: Any val] is SNext[A]
  let _s: {(): Stream[A] val} val

  new val create(s: {(): Stream[A] val} val) =>
    _s = s

  fun mature(): (A, Stream[A] val) ? =>
    let next = _s().force()
    (next.head(), SDelay[A](recover {()(next): Stream[A] val =>
      try next.tail() else SNil[A] end}
    end))

class SMap[A: Any val, B: Any val] is SNext[B]
  let _f: {(A): B} val
  let _s: Stream[A] val

  new val create(f: {(A): B} val, s: Stream[A] val) =>
    _f = f
    _s = s

  fun mature(): (B, Stream[B] val) ? =>
    match _s.force()
    | let cons: SCons[A] val =>
      (_f(cons.head()), SMap[A, B](_f, cons.tail()))
    else
      error
    end

class SFlatMap[A: Any val, B: Any val] is SNext[B]
  let _f: {(A): Stream[B] val} val
  let _s: Stream[A] val
  let _lead_stream: Stream[B] val

  new val create(f: {(A): Stream[B] val} val, s: Stream[A] val,
    lead_stream: Stream[B] val = SNil[B]) =>
    _f = f
    _s = s
    _lead_stream = lead_stream.force()

  fun mature(): (B, Stream[B] val) ? =>
    match _lead_stream
    | let cons: SCons[B] val =>
      (cons.head(), SFlatMap[A, B](_f, _s, cons.tail()))
    else
      let next = _s.force()
      match _f(next.head()).force()
      | let cons: SCons[B] val =>
        (cons.head(), SFlatMap[A, B](_f, next.tail(), cons.tail()))
      else
        SFlatMap[A, B](_f, next.tail(), SNil[B]).mature()
      end
    end

class SFilter[A: Any val] is SNext[A]
  let _pred: {(A): Bool} val
  let _s: Stream[A] val

  new val create(pred: {(A): Bool} val, s: Stream[A] val) =>
    _pred = pred
    _s = s

  fun mature(): (A, Stream[A] val) ? =>
    let s = _s.force()
    if _pred(s.head()) then
      (s.head(), SFilter[A](_pred, s.tail()))
    else
      SFilter[A](_pred, s.tail()).mature()
    end

