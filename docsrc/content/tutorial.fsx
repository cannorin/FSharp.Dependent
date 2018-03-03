(*** hide ***)
// This block of code is omitted in the generated HTML documentation. Use 
// it to define helpers that you do not want to show in the documentation.
//#I "../../src/FSharp.Dependent/bin/Debug"

(**
Introducing your project
========================

Say more

*)
#r "FSharp.Dependent.dll"
open FSharp.Dependent

let private printTypeReadable (s: string) =
  let s = s.Replace('[', '<')
           .Replace(']', '>')
           .Replace("FSharp.Dependent.TypeNats+", "")
           .Replace("FSharp.Dependent.Vectors+", "")
           .Replace("`1", "")
           .Replace("`2", "")
           .Replace(",", ", ")
  printfn "%s" s

open Printf

let three = S(S(S Zero)) // creates a type-level natural 
let four = Nat<4>.value  // you can also use the Nat provider

let seven = three + four // add
let eleven = seven + four

eleven.GetType() |> kprintf printTypeReadable "typeof eleven: %A\n"
// typeof eleven: S<S<S<S<S<S<S<S<S<S<S<Z>>>>>>>>>>>

let eight = eleven - three // subst

eight.GetType() |> kprintf printTypeReadable "typeof eight: %A\n"
// typeof eight: S<S<S<S<S<S<S<S<Z>>>>>>>>

(*
  three - four
  // error FS0001: internal error: Exception of type 'Microsoft.FSharp.Compiler.ConstraintSolver+LocallyAbortOperationThatFailsToResolveOverload' was thrown.
*)

let xs = 1 ^+ 2 ^+ 3 ^+ VNil    // cons-style vector creation
let ys = xs |> Vect.map ((+) 3) // map preserves the size
let zs = Vect.append xs ys |> Vect.tail // append sums the sizes

zs.GetType() |> kprintf printTypeReadable "typeof zs: %A"
// typeof zs: Vect<S<S<S<S<S<Z>>>>>, System.Int32>
zs.vect |> printfn "zs: %A"
// zs: [2; 3; 4; 5; 6]
zs |> Vect.item (eight - four) |> printfn "zs[4] = %A" // type-safe index access!!
// zs[4] = 6
printfn ""

(*  
  zs |> Vect.item eight
  // error FS0001: internal error: Exception of type 'Microsoft.FSharp.Compiler.ConstraintSolver+LocallyAbortOperationThatFailsToResolveOverload' was thrown.

  VNil |> Vect.head
  // error FS0001: Type mismatch. Expecting a
  //    'Vect<Z,'a> -> 'b'
  // but given a
  //    'Vect<S<'c>,'d> -> 'd'
  // The type 'Z' does not match the type 'S<'a>'
*)

let ws = zs |> Vect.take three // take reduces the size

ws.GetType() |> kprintf printTypeReadable "typeof ws: %A"
// typeof ws: Vect<S<S<S<Z>>>, System.Int32>
ws.vect |> printfn "ws: %A"
// ws: [2; 3; 4]
printfn ""

(*
  zs |> Vect.take eleven
  // error FS0001: internal error: Exception of type 'Microsoft.FSharp.Compiler.ConstraintSolver+LocallyAbortOperationThatFailsToResolveOverload' was thrown.
*)

let bs = Vect.init zs.length (fun i -> i % 2 = 0) |> Vect.zip zs
// high compat with List module

bs.GetType() |> kprintf printTypeReadable "typeof bs: %A"
// typeof bs: Vect<S<S<S<S<S<Z>>>>>, System.Tuple<System.Int32, System.Boolean>>
bs.vect |> printfn "bs: %A"
// bs: [(2, true); (3, false); (4, true); (5, false); (6, true)]
printfn ""

(*
  Vect.zip ws bs
  // error FS0001: Type mismatch. Expecting a
  //    'Vect<S<S<S<Z>>>,'a>'
  // but given a
  //    'Vect<S<S<S<S<S<Z>>>>>,(int * bool)>'
  // The type 'Z' does not match the type 'S<S<Z>>'
*)

let cs = zs |> Vect.filter (fun x -> x % 3 = 0) |> Vect.filter (fun x -> x % 2 = 0)
// filter generates upper-bounded sized list
// (simulating existential quantifiers)

let inline printRN (RangedNat(ll, v, ul)) =
  printfn "%i <= (x = %i) <= %i" (natVal ll) v (natVal ul)

// rangeed natural math
cs.length + cs.length |> printRN
// 0 <= (x = 2) <= 10
eight + cs.length |> printRN
// 8 <= (x = 9) <= 13
Vect.append cs xs |> Vect.length |> printRN
// 3 <= (x = 4) <= 8
(0 |> RuntimeNat.LTE <| cs.length) |> printRN
// 0 <= (x = 0) <= 0

printfn ""

open System 
let rnd = new Random()

// returning rangeed naturals
let inline randomLessThan (n: S< ^Nat >) =
  let rand = rnd.Next(0, natVal n - 1)
  rand |> RuntimeNat.LTE <| pred n

randomLessThan eight |> natVal |> printfn "%i < 8"

let inline randomMoreThan (n: ^Nat) =
  let rand = rnd.Next(natVal n + 1, 100)
  rand |> RuntimeNat.GTE <| S n

randomMoreThan eight |> natVal |> printfn "%i > 8"

// ranged naturals can satisfy constraints
zs |> Vect.item (randomLessThan zs.length) |> printfn "%A"

// constraining arguments
let inline PleaseGiveMeLessThan lim x =
  Constraint.LTETerm(x, pred lim);
  printfn "happy with %i" (natVal x)

let inline PleaseGiveMeMoreThan lim x =
  Constraint.GTETerm(x, succ lim);
  printfn "happy with %i" (natVal x)

// win-win transactions
PleaseGiveMeLessThan eight (randomLessThan eight)
PleaseGiveMeMoreThan eight (randomMoreThan eight)


(*** hide ***)
module Console =
  static member ReadLine() = ""
module Number =
  static member tryParse _ = Some 42

let (>>=) x f = Option.bind f x
let readNat name =
  printf "%s > " name;
  Console.ReadLine() |> Number.tryParse |> Option.map SomeNat

// using existential type-level naturals
readNat "input length" >>= mapSomeNat (fun (len: S<SomeNatVariable<"length">>) ->
    let xs = Vect.init len (fun seed -> Random(seed).Next(0,100))
    while true do
      readNat "input index" >>= mapSomeNat (fun (x: RangedNat<Z, SomeNatVariable<"length">>) ->
          xs |> Vect.item x |> printfn "xs[%i] = %i" (natVal x)
        ) |> Option.defaultWith (fun () -> printfn "index is out of range!")
    done
  )

