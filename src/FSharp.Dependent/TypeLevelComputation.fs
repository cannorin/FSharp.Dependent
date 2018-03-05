/// type-level computation.
[<AutoOpen>]
module FSharp.Dependent.TypeLevelComptutation

/// type argument as a term.
[<Struct>]
type TypeArg<'a> = TypeArg of unit

/// wildcard for term-level type argument.
let __<'X> : TypeArg<'X> = TypeArg()

/// lifts type to a term-level type argument.
let TypeArg<'X> : TypeArg<'X> = TypeArg()

/// evaluate type-level expression given as a term-level value.
let inline eval (x: ^X) =
  (^X: (static member eval: ^X -> _) x)

/// converts type to the corresponding term-level value and then evaluate. 
let inline evalSing (_: TypeArg< ^X >) : ^Y =
  eval (sing< ^X >)

