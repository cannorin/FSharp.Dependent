/// Type-level naturals.
[<AutoOpen>]
module FSharp.Dependent.TypeNats

open System

/// Gets a term-level value of the given type-level natural.
let inline natVal (x: ^Nat) =
  (^Nat: (member NatVal: unit -> int) x)

let inline lowerLimitOf (x: ^Nat) : ^Nat' =
  (^Nat: (member Lower: unit -> ^Nat') x)

let inline upperLimitOf (x: ^Nat) : ^Nat' =
  (^Nat: (member Upper: unit -> ^Nat') x)

/// Type-level infinite.
type INF = Inf
  with
    /// Gets the term-level value of this. You can also use `natVal`.
    member inline __.NatVal() = Int32.MaxValue
    /// Internal utility function. Use `+`.
    member inline __.Add _ = Inf
    /// Internal utility function. Never use.
    member inline this.Upper() = this
    /// Internal utility function. Never use.
    member inline this.Lower() = this
    /// Internal utility function. Never use.
    /// Utility field. Ensures that the type-level value and the term-level value are actually the same.
    member inline __.IsStrictNat = true
    static member inline (-) (x: INF, _: _) = x

/// Type-level 0.
type Z = Zero
  with
    /// Gets the term-level value of this. You can also use `natVal`.
    member inline __.NatVal() = 0
    /// Internal utility function. Use `+`.
    member inline __.Add x = x
    /// Internal utility function. Never use.
    member inline this.Upper() = this
    /// Internal utility function. Never use.
    member inline this.Lower() = this
    /// Internal utility function. Never use.
    /// Utility field. Ensures that the type-level value and the term-level value are actually the same.
    member inline __.IsStrictNat = true
    /// We cannot implement custom equality for type-level naturals due to their SRTPs. Use this instead of `=`.
    static member inline (==) (x, y) = natVal x = natVal y
    static member inline (+) (x: ^Nat, y) = 
      (^Nat: (member Add: _ -> _) x, y)
    static member inline (-) (x: ^Nat, _: Z) = x

/// Type-level successor.
type S< ^a when ^a: (member NatVal: unit -> int)> = S of ^a 
  with
    /// Internal utility function. Use `+`.
    member inline this.Add (x: ^NatA) : S< ^NatR > =
      let (S a) = this
      S ( (^NatA: (member Add: _ -> _) x,a) )
    /// Gets the term-level value of this. You can also use `natVal`.
    member inline this.NatVal() =
      let (S a) = this
      1 + (^a: (member NatVal: unit -> int) a)
    /// Internal utility function. Never use.
    member inline this.Upper() = this
    /// Internal utility function. Never use.
    member inline this.Lower() = this
    /// Utility field. Ensures that the type-level value and the term-level value are actually the same.
    member inline __.IsStrictNat = true
    /// We cannot implement custom equality for type-level naturals due to their SRTPs. Use this instead of `=`.
    static member inline (==) (x, y) = natVal x = natVal y
    static member inline (+) (x: ^Nat, y) = 
      (^Nat: (member Add: _ -> _) x, y)
    static member inline (-) (x: S< ^NatX >, y: S< ^NatY >) = let (S x', S y') = (x, y) in x' - y'

/// Range-bounded type-level natural.
type RangedNat< ^LowerLimit, ^UpperLimit
                          when ^UpperLimit: (member NatVal: unit -> int)
                           and ^LowerLimit: (member NatVal: unit -> int)
                           and ^UpperLimit: (member IsStrictNat: bool)
                           and ^LowerLimit: (member IsStrictNat: bool)
                               > =
  /// Do NOT call this construct directly; Use `RuntimeNat` helper module.
  | RangedNat of ^LowerLimit * int * ^UpperLimit
  with
    /// Internal utility function. Never use.
    member inline this.Upper() = let (RangedNat (_, _, upper)) = this in upper
    /// Internal utility function. Never use.
    member inline this.Lower() = let (RangedNat (lower, _, _)) = this in lower
    /// Gets the term-level value of this. You can also use `natVal`.
    member inline this.NatVal() = let (RangedNat (_, i, _)) = this in i
    /// We cannot implement custom equality for type-level naturals due to their SRTPs. Use this instead of `=`.
    static member inline (==) (x, y) = natVal x = natVal y
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

/// Type-level predcessor function.
let inline pred (S x) = x

(*
let inline pred x = 
  let inline pred' (RangedNat (S l, x, S r)) =
    RangedNat (l, x - 1, r)
  RangedNat (lowerLimitOf x, natVal x, upperLimitOf x) |> pred'

  // This breaks the output dll and I don't know why..
  // > warning FS3186: An error occurred while reading the F# metadata node at position 0 in table 'itycons' of assembly 'FSharp.Dependent, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null'. The node had no matching declaration. Please report this warning. You may need to recompile the F# assembly you are using.
*)

/// Type-level predcessor function.
let inline succ x = x + S Zero

module RuntimeNat =
  /// Creates upper-bounded type-level natural whose term-level value is unknown at compile-time.
  ///
  /// ## Description
  ///
  /// This construct is useful when you want to make sure that the return value is unknown at compile-time, but always less than a certain value or equal.
  /// Use this to constrain return types. If you want to make arguments less than a certain value, use `Constraint.LTE` instead.
  ///
  /// ## Example
  ///
  ///   let inline randomLessThan (n: S< ^Nat >) =
  ///     let rand = System.Random().Next(0, natVal n - 1)
  ///     rand |> RuntimeNat.LTE <| pred n
  ///
  /// ## Warning
  ///
  /// This construct is UNSAFE and will throw an InvalidArgumentException if the given value is larger than the specified upper limit.
  let inline LTE (value: int) (upperLimit: ^UpperLimit) : RangedNat< Z, ^UpperLimit' > =
    if value <= natVal upperLimit then
      RangedNat (Zero, value, lowerLimitOf upperLimit)
    else
      invalidArg "value" "the value is greater than the upper limit"

  /// Creates lower-bounded type-level natural whose term-level value is unknown at compile-time.
  ///
  /// ## Description
  ///
  /// This construct is useful when you want to make sure that the return value is unknown at compile-time, but always greater than a certain value or equal.
  /// Use this to constrain return types. If you want to make arguments greater than a certain value, use `Constraint.GTE` instead.
  ///
  /// ## Example
  ///
  ///   let inline randomMoreThan (n: ^Nat) =
  ///     let rand = System.Random().Next(natVal n + 1, System.Int32.MaxValue)
  ///     rand |> RuntimeNat.GTE <| S n
  ///
  /// ## Warning
  ///
  /// This construct is UNSAFE and will throw an InvalidArgumentException if the given value is larger than the specified upper limit.
  let inline GTE (value: int) (lowerLimit: ^LowerLimit) : RangedNat< ^LowerLimit', INF > =
    if value >= natVal lowerLimit then
      RangedNat (upperLimitOf lowerLimit, value, Inf)
    else
      invalidArg "value" "the value is less than the upper limit"


module Constraint =
  /// Helper type function to constrain a certain type-level natural `^NatL` to be less than the specified nat `^NatR` or equal to.
  ///
  /// ## Description
  ///
  /// Although being a bit verbose, using this type is far more performance-wise than just doing ```m - n |> ignore;```
  /// Use this to constrain argument types. If you want to make the return value less than a certain value or equal to, use `RuntimeNat.LTE` instead.
  ///
  /// ## Example
  ///
  ///   let inline pleaseGiveMeLessThan (limit: S< ^NatLimit >) (x: ^NatX) =
  ///     Constraint.LTE< ^NatX, ^NatLimit, _ >;
  ///     printfn "I'm happy with it."
  ///     
  ///   pleaseGiveMeLessThan (S (S Zero)) Zero
  ///
  /// ## Warning
  ///
  ///   Keep the type parameters generic!
  ///   Even if you eta-expand it, the F# typer forcefully solves the constraint.
  ///   Writing member constraints by hands, unfortunately, does not make any improvements here. 
  ///
  ///     > let inline pgmlt3 x = pleaseGiveMeLessThan (S (S (S Zero))) x ;;
  ///     val inline pgmlt3 : x:S<S<Z>> -> unit
  let inline LTE< ^NatL, ^NatR, ^__ when (^NatL or ^NatR): (static member (-): ^NatR -> ^NatL -> ^__)> = ()
 
  /// Short-hand alternative to `Constraint.LTE` that takes term arguments instead of type arguments.
  /// See `Constraint.LTE` for details.
  ///
  /// ## Example
  ///
  /// The formar example can be re-written as:
  ///
  ///   let inline pleaseGiveMeLessThan limit x =
  ///     Constraint.LTETerm(x, pred limit);
  ///     printfn "I'm happy with it."
  let inline LTETerm (_: ^NatL, _: ^NatR) = LTE< ^NatL, ^NatR, _ >

  /// Helper type function to constrain a certain type-level natural `^NatL` to be greater than the specified nat `^NatR` or equal to.
  ///
  /// ## Description
  ///
  /// Although being a bit verbose, using this type is far more performance-wise than just doing ```m - n |> ignore;```
  /// Use this to constrain argument types. If you want to make the return value greater than a certain value or equal to, use `RuntimeNat.GTE` instead.
  ///
  /// ## Example
  ///
  ///   let inline pleaseGiveMeMoreThan (limit: ^NatLimit) (x: ^NatX) =
  ///     Constraint.GTE< ^NatX, S< ^NatLimit >, _ >;
  ///     printfn "I'm happy with it."
  ///     
  ///   pleaseGiveMeMoreThan (S Zero) (S (S Zero))
  ///
  /// ## Warning
  ///
  ///   Keep the type parameters generic!
  ///   Even if you eta-expand it, the F# typer forcefully solves the constraint.
  ///   Writing member constraints by hands, unfortunately, does not make any improvements here. 
  ///
  ///     > let inline pgmmt1 x = pleaseGiveMeMoreThan (S Zero) x ;;
  ///     val inline pgmmt1 : x:S<S<Z>> -> unit
  let inline GTE< ^NatL, ^NatR, ^__ when (^NatL or ^NatR): (static member (-): ^NatL -> ^NatR -> ^__)> = ()

  /// Short-hand alternative to `Constraint.GTE` that takes term arguments instead of type arguments.
  /// See `Constraint.GTE` for details.
  ///
  /// ## Example
  ///
  /// The formar example can be re-written as:
  ///
  ///   let inline pleaseGiveMeMoreThan limit x =
  ///     Constraint.GTETerm(x, succ limit);
  ///     printfn "I'm happy with it."
  let inline GTETerm (_: ^NatL, _: ^NatR) = GTE< ^NatL, ^NatR, _ >
