FSharp.Dependent
======================

The FSharp.Dependent library can be [installed from NuGet](ttps://nuget.org/packages/FSharp.Dependent)

  PM> Install-Package FSharp.Dependent

This library simulates [Dependent Types](https://en.m.wikipedia.org/wiki/Dependent_type) in F# using type-level natural numbers and (ab)using inline functions.

Example
-------

```fsharp
#r "FSharp.Dependent.dll"
open FSharp.Dependent

let three = Nat<3>.value
let eight = Nat<8>.value

let eleven = three + eight
// let err = three - eight
// error FS0001: internal error: Exception of type 'Microsoft.FSharp.Compiler.ConstraintSolver+LocallyAbortOperationThatFailsToResolveOverload' was thrown.

let xs = 1 ^+ 2 ^+ 3 ^+ 4 ^+ VNil
let ys = Vect.init three id |> Vect.map ((+) 5)

let zs = Vect.append xs ys
zs |> Vect.item Nat<5>.value |> printfn "%i" // 6
// zs |> Vect.item eleven |> printfn "%i"
// error FS0001: internal error: Exception of type 'Microsoft.FSharp.Compiler.ConstraintSolver+LocallyAbortOperationThatFailsToResolveOverload' was thrown.

1 ^+ Vect.empty |> Vect.head |> printfn "%i" // 1
// Vect.empty |> Vect.head |> printfn "%i"
// error FS0001: Type mismatch. Expecting a
//    'Vect<Z,'a> -> 'b'
// but given a
//    'Vect<Z,'c> -> 'c'
// This expression was expected to have type
//    'S<'a>'
// but here has type
//    'Z'

let inline randomLessThan n =
  let rand = System.Random().Next(0, natVal n - 1)
  rand |> RuntimeNat.LTE <| pred n // existential quantifier simulation

zs |> Vect.item (randomLessThan zs.length) |> printfn "%i"

let inline pleaseGiveMeLessThan limit x =
  Constraint.LTETerm(x, pred limit); // this does nothing in term-level but adds a constraint in type level, here abuses F#'s constraint solver!
  printfn "I'm happy with %i." (natVal x)

zs.length |> pleaseGiveMeLessThan eleven // I'm happy with 7.

let inline winwin x = randomLessThan x |> pleaseGiveMeLessThan x

winwin eight
```

Samples & documentation
-----------------------

The library comes with comprehensible documentation. 
It can include tutorials automatically generated from `*.fsx` files in [the content folder][content]. 
The API reference is automatically generated from Markdown comments in the library implementation.

 * [Tutorial](tutorial.html) contains a further explanation of this sample library.

 * [API Reference](reference/index.html) contains automatically generated documentation for all types, modules
   and functions in the library. This includes additional brief samples on using most of the
   functions.
 
Contributing and copyright
--------------------------

The project is hosted on [GitHub][gh] where you can [report issues][issues], fork 
the project and submit pull requests. If you're adding a new public API, please also 
consider adding [samples][content] that can be turned into a documentation. You might
also want to read the [library design notes][readme] to understand how it works.

The library is available under Public Domain license, which allows modification and 
redistribution for both commercial and non-commercial purposes. For more information see the 
[License file][license] in the GitHub repository. 

  [content]: https://github.com/cannorin/FSharp.Dependent/tree/master/docs/content
  [gh]: https://github.com/cannorin/FSharp.Dependent
  [issues]: https://github.com/cannorin/FSharp.Dependent/issues
  [readme]: https://github.com/cannorin/FSharp.Dependent/blob/master/README.md
  [license]: https://github.com/cannorin/FSharp.Dependent/blob/master/LICENSE.txt
