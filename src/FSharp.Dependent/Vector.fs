/// Fixed-length vector types (size-dependent lists).
[<AutoOpen>]
module FSharp.Dependent.Vectors

/// Fixed-length vectors.
[<Struct>]
type Vect< ^Nat, 'a when ^Nat: (member NatVal: unit -> int)> = { length: ^Nat; vect: 'a list }

/// Vector terminator.
let VNil: Vect<Z, 'a> = { length = Zero; vect = [] }

/// Vector constructor.
let inline VCons (a: 'a) (xs: Vect< ^Nat, 'a >) : Vect<S< ^Nat >, 'a> = { length = S xs.length; vect = a :: xs.vect }

/// I wish I could use `::` instead of `^+`.
///
/// ## Example
///
///   let xs = 1 ^+ 2 ^+ 3 ^+ VNil
let inline (^+) (a: 'a) (xs: Vect< ^Nat, 'a >) : Vect<S< ^Nat >, 'a> = { length = S xs.length; vect = a :: xs.vect }

/// Vector utility functions.
/// Clone of size-sensitive functions from the List module.
module Vect =
  let empty = VNil

  let inline length (xs: Vect<_,_>) = xs.length
  
  let inline map f (xs: Vect< ^Nat, 'a >)  =
    { length = xs.length; vect = xs.vect |> List.map f }

  /// Typer will fail if the length of `xs` is not the same as that of `ys`. 
  let inline map2 f (xs: Vect< ^Nat, 'a >) (ys: Vect< ^Nat, 'b >) : _
    when ^Nat: (member IsStrictNat: bool) =
    { length = xs.length; vect = List.map2 f xs.vect ys.vect }
 
  /// Typer will fail unless `xs`, `ys`, and `zs` have the same length.
  let inline map3 f (xs: Vect< ^Nat, 'a >) (ys: Vect< ^Nat, 'b >) (zs: Vect< ^Nat, 'c >) : _
    when ^Nat: (member IsStrictNat: bool) =
    { length = xs.length; vect = List.map3 f xs.vect ys.vect zs.vect }
 
  let inline mapi f (xs: Vect< ^Nat, 'a >)  =
    { length = xs.length; vect = xs.vect |> List.mapi f }

  /// Typer will fail if the length of `xs` is not the same as that of `ys`. 
  let inline mapi2 f (xs: Vect< ^Nat, 'a >) (ys: Vect< ^Nat, 'b >) : _
    when ^Nat: (member IsStrictNat: bool) =
    { length = xs.length; vect = List.mapi2 f xs.vect ys.vect }

  /// Typer will fail if the length of `xs` is not the same as that of `ys`. 
  let inline iter2 f (xs: Vect< ^Nat, 'a >) (ys: Vect< ^Nat, 'b >) : _
    when ^Nat: (member IsStrictNat: bool) =
    List.iter2 f xs.vect ys.vect
  
  /// Typer will fail if the length of `xs` is not the same as that of `ys`. 
  let inline iteri2 f (xs: Vect< ^Nat, 'a >) (ys: Vect< ^Nat, 'b >) : _
    when ^Nat: (member IsStrictNat: bool) =
    List.iteri2 f xs.vect ys.vect

  /// Typer will fail if the length of `xs` is not the same as that of `ys`. 
  let inline fold2 f state (xs: Vect< ^Nat, 'a >) (ys: Vect< ^Nat, 'b >) : _
    when ^Nat: (member IsStrictNat: bool) =
      List.fold2 f state xs.vect ys.vect

  /// Typer will fail if the length of `xs` is not the same as that of `ys`. 
  let inline foldBack2 f (xs: Vect< ^Nat, 'a >) (ys: Vect< ^Nat, 'b >) state : _
    when ^Nat: (member IsStrictNat: bool) =
      List.foldBack2 f xs.vect ys.vect state

  let inline scan f state (xs: Vect< ^Nat, 'a >) : Vect<S< ^Nat >, 'a> =
    let xs' = xs.vect |> List.scan f state
    { length = S xs.length; vect = xs' }

  let inline filter (f: 'a -> bool)  (xs: Vect< ^Nat, 'a >) : Vect<RangedNat< Z, ^Nat' >, 'a> =
    let xs' = xs.vect |> List.filter f
    let len' = List.length xs' |> RuntimeNat.LTE <| upperLimitOf xs.length
    { length = len'; vect = xs' }

  let inline partition (f: 'a -> bool)  (xs: Vect< ^Nat, 'a >) : Vect<RangedNat< Z, ^Nat' >, 'a> * Vect<RangedNat< Z, ^Nat' >, 'a> =
    let (xs', ys') = xs.vect |> List.partition f
    let len1 = List.length xs' |> RuntimeNat.LTE <| upperLimitOf xs.length
    let len2 = List.length ys' |> RuntimeNat.LTE <| upperLimitOf xs.length
    ({ length = len1; vect = xs' }, { length = len2; vect = ys' })

  /// Typer will fail if the length of `xs` is not the same as that of `ys`. 
  let inline forall2 f (xs: Vect< ^Nat, 'a >) (ys: Vect< ^Nat, 'b >) : _
    when ^Nat: (member IsStrictNat: bool) =
      List.forall2 f xs.vect ys.vect

  /// Typer will fail if the length of `xs` is not the same as that of `ys`. 
  let inline exists2 f (xs: Vect< ^Nat, 'a >) (ys: Vect< ^Nat, 'b >) : _
    when ^Nat: (member IsStrictNat: bool) =
      List.exists2 f xs.vect ys.vect

  let inline findIndex f (xs: Vect<S< ^Nat >, _>) : RangedNat< Z, ^Nat > =
    let index = List.findIndex f xs.vect
    index |> RuntimeNat.LTE <| pred xs.length

  let inline tryFindIndex f (xs: Vect< ^Nat, _>) : RangedNat< Z, ^Nat' > option =
    let index = List.tryFindIndex f xs.vect
    index |> Option.map (fun i -> i |> RuntimeNat.LTE <| (upperLimitOf xs.length |> pred))

  let inline choose (f: 'a -> 'b option) (xs: Vect< ^Nat, 'a >) : Vect<RangedNat< Z, ^Nat' >, 'b> =
    let xs' = xs.vect |> List.choose f
    let len' = List.length xs' |> RuntimeNat.LTE <| upperLimitOf xs.length
    { length = len'; vect = xs' }

  let inline chunkBySize (n: ^NatN) (xs: Vect< ^NatXS, 'a >) : Vect<RangedNat< Z, ^NatXS' >, Vect<RangedNat< Z, ^NatN' >, 'a>> =
    Constraint.LTETerm(S Zero, lowerLimitOf n);
    let xss = xs.vect |> List.chunkBySize (natVal n)
    let chunks = List.length xss |> RuntimeNat.LTE <| upperLimitOf xs.length
    { length = chunks; vect = xss |> List.map (fun xs -> { length = List.length xs |> RuntimeNat.LTE <| upperLimitOf n; vect = xs }) }

  let inline countBy f (xs: Vect<_, _>) =
    let xs' = xs.vect |> List.countBy f
    { length = List.length xs' |> RuntimeNat.LTE <| upperLimitOf xs.length; vect = xs' }

  let inline distinct (xs: Vect<_, _>) =
    let xs' = xs.vect |> List.distinct
    { length = List.length xs' |> RuntimeNat.LTE <| upperLimitOf xs.length; vect = xs' }

  let inline snoc (a: 'a) (xs: Vect< ^Nat, 'a >) : Vect< S< ^Nat >, 'a > =
    { length = S xs.length; vect = List.append xs.vect [a] }

  let inline append (xs: Vect< ^NatX, 'a >) (ys: Vect< ^NatY, 'a >) : Vect< _, 'a >=
    { length = xs.length + ys.length; vect = List.append xs.vect ys.vect }

  /// Typer will fail if `xs` is `VNil`. 
  let inline head (xs: Vect< ^Nat, _>) =
    Constraint.GTETerm(lowerLimitOf xs.length, S Zero)
    List.head xs.vect

  /// Typer will fail if `xs` is `VNil`. 
  let inline tail (xs: Vect< ^Nat, _>) =
    Constraint.GTETerm(lowerLimitOf xs.length, S Zero)
    { length = pred xs.length; vect = List.tail xs.vect }

  /// Typer will fail if `n` is out of range of `xs`.
  let inline take (n: ^NatN) (xs: Vect< ^NatXS, 'a>) =
    Constraint.LTETerm(n, lowerLimitOf xs.length); 
    { length = n; vect = xs.vect |> List.take (natVal n) }

  /// Typer will fail if `n` is out of range of `xs`.
  /// Be aware that `n` start from 0.
  let inline item (n: ^NatN) (xs: Vect< ^NatXS, 'a>) =
    Constraint.LTETerm(n, lowerLimitOf xs.length |> pred);
    xs.vect |> List.item (natVal n)

  let inline init (n: ^Nat) (f: int -> 'a) : Vect< ^Nat, 'a> =
    let n' = natVal n
    { length = n; vect = List.init n' f }

  let inline replicate (n: ^Nat) (x: 'a) = init n (fun _ -> x)

  let inline rev xs = { length = xs.length; vect = xs.vect |> List.rev }

  let inline sort xs = { length = xs.length; vect = xs.vect |> List.sort }
  
  let inline sortBy proj xs = { length = xs.length; vect = xs.vect |> List.sortBy proj }
  
  let inline sortWith comp xs = { length = xs.length; vect = xs.vect |> List.sortWith comp }

  /// Typer will fail if the length of `xs` is not the same as that of `ys`. 
  let inline zip (xs: Vect< ^Nat, 'a >) (ys: Vect< ^Nat, 'b >) : Vect< ^Nat, ( 'a * 'b )>
    when ^Nat: (member IsStrictNat: bool) =
    { length = xs.length; vect = List.zip xs.vect ys.vect }

  /// Typer will fail unless `xs`, `ys`, and `zs` have the same length.
  let inline zip3 (xs: Vect< ^Nat, 'a >)
                  (ys: Vect< ^Nat, 'b >)
                  (zs: Vect< ^Nat, 'c >) : Vect< ^Nat, ( 'a * 'b * 'c ) >
    when ^Nat: (member IsStrictNat: bool) =
    { length = xs.length; vect = List.zip3 xs.vect ys.vect zs.vect }

  let inline unzip xys = 
    let (xs', ys') = xys.vect |> List.unzip
    ({ length = xys.length; vect = xs' }, { length = xys.length; vect = ys' })

  let inline unzip3 xyzs =
    let (xs', ys', zs') = xyzs.vect |> List.unzip3
    (
      { length = xyzs.length; vect = xs' },
      { length = xyzs.length; vect = ys' },
      { length = xyzs.length; vect = zs' }
    )

  let inline toList (xs: Vect<_, _>) = xs.vect

  /// Try to create `Vect` from `List` with the given length `n`.
  let inline tryOfList (n: ^Nat) (xs: 'a list) =
    if (^Nat: (member NatVal: unit -> int) n) = List.length xs then
      Some { length = n; vect = xs }
    else
      None

