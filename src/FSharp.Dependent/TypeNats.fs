/// Type-level naturals.
[<AutoOpen>]
module FSharp.Dependent.TypeNats

open System

type IStrictNat = interface end

/// Gets an integer value of the given type-level natural.
let inline natVal (x: ^X) : int
  when ^X: (static member eval: ^X -> ^Nat) =
  (^Nat: (static member natVal: ^Nat -> int) (eval x))

let inline tryCast< ^Nat when ^Nat: (static member tryCast: ^Nat * int -> ^Nat option) > i =
  (^Nat: (static member tryCast: ^Nat * int -> ^Nat option) Unchecked.defaultof< ^Nat >,i)

let inline lowerLimitOf (x: ^Nat) : ^Nat' =
  (^Nat: (member Lower: unit -> ^Nat') x)

let inline upperLimitOf (x: ^Nat) : ^Nat' =
  (^Nat: (member Upper: unit -> ^Nat') x)

/// Type-level predcessor function.
let inline pred (x: ^Nat) =
  (^Nat: (static member pred: _ -> _) x)

// Type-level predcessor function.
let inline succ (x: ^Nat) =
  (^Nat: (static member succ:_ -> _) x)

let inline (>=^) x y =
  (x >^ y) ||^ (x =^ y)

let inline (<=^) x y =
  (x <^ y) ||^ (x =^ y)

/// Type-level infinite.
type INF = Inf
  with
    interface IStrictNat
    /// Internal utility function. Use `+`.
    member inline __.Add _ = Inf
    /// Internal utility function. Never use.
    member inline this.Upper() = this
    /// Internal utility function. Never use.
    member inline this.Lower() = this
    static member inline (-) (x: INF, _) = x
    static member inline (>^) (_: INF, _) = True
    static member inline (<^) (_: INF, _) = False
    static member inline (=^) (Inf, Inf) = True
    static member inline pred (Inf) = Inf
    static member inline succ (Inf) = Inf
    static member inline sing (_: INF) = Inf
    static member inline eval (_: INF) = Inf
    static member inline natVal (_: INF) = Int32.MaxValue

/// Type-level successor.
type S< 'a > =
  | S of 'a 
  with
    /// Internal utility function. Use `+`.
    member inline this.Add (x: ^NatA) : S< ^NatR > =
      let (S a) = this
      S ( (^NatA: (member Add: _ -> _) x,a) )
    /// Internal utility function. Never use.
    member inline this.Upper() = this
    /// Internal utility function. Never use.
    member inline this.Lower() = this
    /// We cannot implement custom equality for type-level naturals due to their SRTPs. Use this instead of `=`.
    static member inline (=^) (S x, S y) = x =^ y 
    static member inline (=^) (_, Inf) = False
    static member inline (=^) (Inf, _) = False
    static member inline (>^) (S x, S y) = x >^ y 
    static member inline (>^) (_, Inf) = False
    static member inline (<^) (S x, S y) = x <^ y 
    static member inline (<^) (_, Inf) = True
    static member inline (+) (S x : S< ^X >, y) = S (^X: (static member (+): ^X * _ -> _) x,y)
    static member inline (-) (S x, S y) = x - y
    static member inline pred (S x) = x
    static member inline succ (x: S<_>) = S x
    static member inline sing (_: S< ^X >) =
      S (^X: (static member sing: ^X -> _) Unchecked.defaultof< ^X >)
    static member inline eval (S x) = S (eval x)
    static member inline natVal (x: S< ^X >) =
      let (S x') = x in
      1 + (^X: (static member natVal: ^X -> int) x')
    static member inline tryCast (_: S< ^X >, i) : S< ^X > option =
      if i <= 0 then None
      else
        (^X: (static member tryCast: ^X * int -> ^X option) Unchecked.defaultof< ^X >,(i-1)) |> Option.map S
    interface IStrictNat
    
/// Type-level 0.
type Z = Zero
  with
    /// Internal utility function. Use `+`.
    member inline __.Add x = x
    /// Internal utility function. Never use.
    member inline this.Upper() = this
    /// Internal utility function. Never use.
    member inline this.Lower() = this
    /// We cannot implement custom equality for type-level naturals due to their SRTPs. Use this instead of `=`.
    static member inline (=^) (Zero, Zero) = True
    static member inline (=^) (S _, _) = False
    static member inline (=^) (_, S _) = False
    static member inline (=^) (Inf, _) = False
    static member inline (=^) (_, Inf) = False
    static member inline (>^) (Inf, _) = True
    static member inline (>^) (S _, Zero) = True
    static member inline (>^) (_, Inf) = False
    static member inline (>^) (Zero, _) = False
    static member inline (<^) (Inf, _) = False
    static member inline (<^) (_, Zero) = False
    static member inline (<^) (Zero, S _) = True
    static member inline (<^) (_, Inf) = True
    static member inline (+) (Zero, y) = y
    static member inline (-) (x: ^Nat, _: Z) = x
    static member inline succ Zero = S Zero
    static member inline sing (_: Z) = Zero
    static member inline eval (_: Z) = Zero
    static member inline natVal (_: Z) = 0
    static member inline tryCast (_: Z, i) = if i = 0 then Some Zero else None
    interface IStrictNat

/// Range-bounded type-level natural.
type RangedNat< 'LowerLimit, 'UpperLimit
                          when 'UpperLimit :> IStrictNat
                           and 'LowerLimit :> IStrictNat
                               > =
  /// Do NOT call this construct directly; Use `RuntimeNat` helper module.
  | RangedNat of 'LowerLimit * int * 'UpperLimit
  with
    /// Internal utility function. Never use.
    member inline this.Upper() = let (RangedNat (_, _, upper)) = this in upper
    /// Internal utility function. Never use.
    member inline this.Lower() = let (RangedNat (lower, _, _)) = this in lower
    static member inline natVal (RangedNat(_, x, _)) = x
    /// We cannot implement custom equality for type-level naturals due to their SRTPs. Use this instead of `=`.
    static member inline (=^) (RangedNat(lx, _, ux), RangedNat(ly, _, uy)) = And(lx =^ ly, ux =^ uy) |> eval
    static member inline (+) (x: RangedNat< ^NatX1, ^NatX2>, y: ^NatY) =
      let (RangedNat (lower_x, x', upper_x)) = x
      let y' = natVal y
      RangedNat(
          (^NatX1: (member Add: ^NatY -> _) lower_x,y),
          x' + y', 
          (^NatX2: (member Add: ^NatY -> _) upper_x,y)
        )
    static member inline (+) (x: ^NatX, y: RangedNat< ^NatY1, ^NatY2>) =
      let (RangedNat (lower_y, y', upper_y)) = y
      let x' = natVal x
      RangedNat(
          (^NatY1: (member Add: ^NatX -> _) lower_y,x),
          x' + y', 
          (^NatY2: (member Add: ^NatX -> _) upper_y,x)
        )
    static member inline (+) (x: RangedNat<_,_>, y: RangedNat<_,_>) =
      let (RangedNat (lower_x, x', upper_x)) = x
      let (RangedNat (lower_y, y', upper_y)) = y
      RangedNat(lower_x + lower_y, x' + y', upper_x + upper_y)
    member inline this.Add x = this + x
    static member inline (-) (x: ^NatX, y: RangedNat<_, ^Upper>) : RangedNat<_,_>
      when (^NatX or ^Upper): (static member (-): ^NatX -> ^Upper -> _) =
      let (RangedNat (lower, y', _)) = y in
      RangedNat (x - lower, natVal x - y', x)
    static member inline (-) (x: RangedNat< ^Lower, _>, y: ^NatY) : RangedNat<_,_>
      when (^NatY or ^Lower): (static member (-): ^Lower -> ^NatY -> _) =
      let (RangedNat(lower, x', upper)) = x in
      RangedNat (lower - y, x' - natVal y, upper - y)
    static member inline pred (RangedNat(S lower, x, S upper)) =
      RangedNat (lower, x-1, upper)
    static member inline succ (RangedNat(lower, x, upper)) =
      RangedNat (S lower, x+1, S upper)
    static member inline eval (RangedNat(lower, x, upper) : RangedNat< ^Lower, ^Upper >) =
      RangedNat (eval lower, x, eval upper)
    static member inline tryCast(_: RangedNat< ^Lower, ^Upper >, i) =
      let lower = sing< ^Lower >
      let upper = sing< ^Upper >
      if natVal lower <= i && i <= natVal upper then
        RangedNat(lower, i, upper) |> Some
      else
        None

module Constraint =
  /// Helper type function to constrain a certain type-level natural NatL to be less than the specified nat NatR or equal to.
  let inline LTE< ^NatL, ^NatR, ^__ when ^NatL: (static member (-): ^NatR -> ^NatL -> ^__)
                                    and ^NatL: (static member natVal: ^NatL -> int)
                                    and ^NatR: (static member natVal: ^NatR -> int) > = ()
 
  /// Short-hand alternative to `Constraint.LTE` that takes term arguments instead of type arguments.
  let inline LTETerm (_: ^NatL, _: ^NatR) = LTE< ^NatL, ^NatR, _ >

  /// Helper type function to constrain a certain type-level natural NatL to be greater than the specified nat NatR or equal to.
  let inline GTE< ^NatL, ^NatR, ^__ when ^NatL: (static member (-): ^NatL -> ^NatR -> ^__)
                                    and ^NatL: (static member natVal: ^NatL -> int)
                                    and ^NatR: (static member natVal: ^NatR -> int) > = ()

  /// Short-hand alternative to `Constraint.GTE` that takes term arguments instead of type arguments.
  let inline GTETerm (_: ^NatL, _: ^NatR) = GTE< ^NatL, ^NatR, _ >

  let inline Eq< ^NatL, ^NatR when ^NatL: (static member (=^): ^NatL -> ^NatR -> bool)
                                    and ^NatL: (static member natVal: ^NatL -> int)
                                    and ^NatR: (static member natVal: ^NatR -> int) > = ()

  let inline EqTerm (_: ^NatL, _: ^NatR) = Eq< ^NatL, ^NatR >


module RuntimeNat =
  /// Creates upper-bounded type-level natural whose term-level value is unknown at compile-time.
  let inline LTE (value: int) (upperLimit: ^UpperLimit) : RangedNat< Z, ^UpperLimit' > =
    if value <= natVal upperLimit then
      RangedNat (Zero, value, lowerLimitOf upperLimit)
    else
      invalidArg "value" "the value is greater than the upper limit"

  /// Creates lower-bounded type-level natural whose term-level value is unknown at compile-time.
  let inline GTE (value: int) (lowerLimit: ^LowerLimit) : RangedNat< ^LowerLimit', INF > =
    if value >= natVal lowerLimit then
      RangedNat (upperLimitOf lowerLimit, value, Inf)
    else
      invalidArg "value" "the value is less than the upper limit"

  /// Creates ranged type-level natural whose term-level value is unknown at compile-time.
  let inline Ranged (value: int) (lowerLimit: ^LowerLimit) (upperLimit: ^UpperLimit) =
    Constraint.LTETerm(lowerLimit, upperLimit);
    if value <= natVal upperLimit && value >= natVal lowerLimit then
      RangedNat (upperLimitOf lowerLimit, value, lowerLimitOf upperLimit)
    else
      invalidArg "value" "the value is not within the given range"
