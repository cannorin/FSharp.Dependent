(*** hide ***)
// This block of code is omitted in the generated HTML documentation. Use 
// it to define helpers that you do not want to show in the documentation.
//#I "../../src/FSharp.Dependent/bin/Debug"

(**
FSharp.Dependent
======================

Documentation

<div class="row">
  <div class="span1"></div>
  <div class="span6">
    <div class="well well-small" id="nuget">
      The FSharp.Dependent library can be <a href="https://nuget.org/packages/FSharp.Dependent">installed from NuGet</a>:
      <pre>PM> Install-Package FSharp.Dependent</pre>
    </div>
  </div>
  <div class="span1"></div>
</div>

This library simulates [Dependent Types](https://en.m.wikipedia.org/wiki/Dependent_type) in F# using type-level natural numbers and (ab)using inline functions.

Example
-------

*)
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

open System

let inline randomLessThan n =
  let rand = Random().Next(0, natVal n - 1)
  rand |> RuntimeNat.LTE <| pred n // existential quantifier simulation

zs |> Vect.item (randomLessThan zs.length) |> printfn "%i"

let inline pleaseGiveMeLessThan limit x =
  Constraint.LTETerm(x, pred limit); // this does nothing in term-level but adds a constraint in type level, here abuses F#'s constraint solver!
  printfn "I'm happy with %i." (natVal x)

zs.length |> pleaseGiveMeLessThan eleven // I'm happy with 7.

let inline winwin x = randomLessThan x |> pleaseGiveMeLessThan x

winwin eight

(*** hide ***)
module Console =
  static member ReadLine() = ""
module Number =
  static member tryParse _ = Some 42

let (>>=) x f = Option.bind f x
let readNat name =
  printf "%s > " name;
  Console.ReadLine() |> Number.tryParse |> Option.map SomeNat

readNat "input length" >>= mapSomeNat (fun (len: S<SomeNatVariable<"length">>) ->
    let xs = Vect.init len (fun seed -> Random(seed).Next(0,100))
    while true do
      readNat "input index" >>= mapSomeNat (fun (x: RangedNat<Z, SomeNatVariable<"length">>) ->
          xs |> Vect.item x |> printfn "xs[%i] = %i" (natVal x)
        ) |> Option.defaultWith (fun () -> printfn "index is out of range!")
    done
  )

(**
Some more info

Samples & documentation
-----------------------

The library comes with comprehensible documentation. 
It can include tutorials automatically generated from `*.fsx` files in [the content folder][content]. 
The API reference is automatically generated from Markdown comments in the library implementation.

 * [Tutorial](tutorial.html) contains a further explanation of this sample library.

 * [API Reference](reference/index.html) contains automatically generated documentation for all types, modules
   and functions in the library. This includes additional brief samples on using most of the
   functions.

 * [Using Constraints and Ranged Naturals](using-constraints.html)
 
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
*)
