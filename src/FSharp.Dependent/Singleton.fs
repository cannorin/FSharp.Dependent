/// maps term-level values and type-level values.
[<AutoOpen>]
module FSharp.Dependent.Singleton

[<Struct>]
type Sing< ^A when ^A: (static member sing: unit -> ^A) > = Sing_ with
  static member inline sing() =
    (^A: (static member sing: unit -> ^A) ())

let inline sing< ^A when ^A: (static member sing: unit -> ^A) > =
  Sing< ^A >.sing()

let inline singThat< ^A when ^A: (static member sing: unit -> ^A) > (predicate: ^A -> bool) : ^A option =
  let a = Sing< ^A >.sing()
  if predicate a then Some a else None

()