[<AutoOpen>]
module FSharp.Dependent.SomeNat
open System
open System.IO
open System.Reflection
open FSharp.Core.CompilerServices
open FSharp.Dependent.TypeNats
open Microsoft.FSharp.Control
open Microsoft.FSharp.Collections
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Reflection
open ProviderImplementation
open ProviderImplementation.ProvidedTypes

/// Existential type-level naturals.
type SomeNat = SomeNat of int with
  interface IStrictNat
  /// Internal utility function. Use `+`.
  member inline this.Add (x: ^NatA) : ^NatR =
    (^NatA: (member Add: _ -> _) x,this)
  static member inline (-) (x: S< ^X >, n: ^N) : S< ^R >
    when (^X or ^N): (static member (-): ^X * ^N -> ^R) =
    let (S x') = x in
    S ((^X or ^N): (static member (-): _ * _ -> _) x',n)
  static member inline (+) (SomeNat m, SomeNat n) = SomeNat (m+n)
  static member inline (+) (x, Zero) = x
  static member inline (+) (x, S y) = S (x + y)
  static member inline succ x = S x
  static member inline natVal (SomeNat i) = i
  static member inline eval x = x

/// Do not use.
module SomeNatInternal =
  let mutable someNatVariableCache : Map<string, int option> = Map.empty

open SomeNatInternal

/// Take a SomeNat and try to treat as the specified type-level variable.
let inline mapSomeNat (exec: ^Nat -> ^a) sn : ^a option =
  try
    let oldMap = someNatVariableCache
    let ret = 
      match (tryCast< ^Nat > (natVal sn)) with
        | Some x -> exec x |> Some
        | None -> None
    someNatVariableCache <- oldMap
    ret
  with
    | _ -> None

/// Take an integer and try to treat as the specified type-level variable.
let inline withSomeNat (i: int) (exec: ^Nat -> ^a) : ^a option =
  mapSomeNat exec (SomeNat i)

[<TypeProvider>]
type SomeNatVariableProvider(cfg) as this =
  inherit TypeProviderForNamespaces(cfg)
  let thisAsm = Assembly.GetExecutingAssembly()
  let root = "FSharp.Dependent"
  let baseTy = typeof<SomeNat>
  let prm = [ProvidedStaticParameter("name", typeof<string>)]
  let ty = ProvidedTypeDefinition(thisAsm, root, "SomeNatVariable", Some baseTy)
  do ty.AddXmlDoc "Capture SomeNat as a unique type variable."
  do ty.DefineStaticParameters(
      parameters = prm,
      instantiationFunction = (fun tyName prmValues ->
        match prmValues with
          | [| :? string as name |] ->
            let ty = ProvidedTypeDefinition(thisAsm, root, tyName, baseType = Some baseTy)

            let tryGet = <@@ someNatVariableCache |> Map.tryFind (%%Expr.Value(name) : string) |> Option.flatten @@>
            let set = <@@ fun i -> someNatVariableCache <- (someNatVariableCache |> Map.add (%%Expr.Value(name) : string) i) @@>
            ProvidedMethod(
                "tryCast", 
                [
                  ProvidedParameter("dummy", ty);
                  ProvidedParameter("value", typeof<int>)
                ],
                typedefof<option<_>>.MakeGenericType(ty),
                invokeCode = (fun [_; v] ->
                  <@@
                      let n = (%%v : int) in
                      match (%%tryGet : int option) with
                        | Some m when n = m -> Some (SomeNat n)
                        | None -> (%%set : int option -> unit) (Some n); Some (SomeNat n)
                        | _ -> None
                  @@>),
                isStatic = true
              ) |> ty.AddMember
 
            ProvidedMethod(
                "sing",
                [ProvidedParameter("dummy", ty)],
                ty,
                isStatic = true,
                invokeCode = fun _ ->
                  <@@
                    match (%%tryGet : int option) with
                      | Some n -> SomeNat n
                      | None -> failwithf "the type variable '%s' has not yet been bounded." name
                  @@>
              ) |> ty.AddMember
            
            ProvidedMethod(
                "Lower",
                [],
                ty,
                isStatic = true,
                invokeCode = fun _ ->
                  <@@
                    match (%%tryGet : int option) with
                      | Some n -> SomeNat n
                      | None -> failwithf "the type variable '%s' has not yet been bounded." name
                  @@>
              ) |> ty.AddMember
            
            ProvidedMethod(
                "Upper",
                [],
                ty,
                isStatic = true,
                invokeCode = fun _ ->
                  <@@
                    match (%%tryGet : int option) with
                      | Some n -> SomeNat n
                      | None -> failwithf "the type variable '%s' has not yet been bounded." name
                  @@>
              ) |> ty.AddMember

            ProvidedMethod(
                "succ",
                [ProvidedParameter("value", ty)],
                (typedefof<S<_>>.MakeGenericType(ty)),
                isStatic = true,
                invokeCode = fun [x] ->
                  <@@
                    S (%%x : SomeNat)
                  @@>
              ) |> ty.AddMember

            ProvidedMethod("resetCache", [], typeof<unit>, isStatic = true, invokeCode = fun _ -> <@@ (%%set: int option -> unit) None @@>) |> ty.AddMember

            ProvidedMethod(
                "op_EqualsHat",
                [
                  ProvidedParameter("x", ty);
                  ProvidedParameter("y", ty)
                ],
                typeof<True>,
                invokeCode = (fun _ -> <@@ True @@>),
                isStatic = true
              ) |> ty.AddMember 
            
            ProvidedMethod(
                "op_Subtraction",
                [
                  ProvidedParameter("x", ty);
                  ProvidedParameter("y", ty)
                ],
                typeof<Z>,
                invokeCode = (fun _ -> <@@ Zero @@>),
                isStatic = true
              ) |> ty.AddMember 
            ty
          | _ -> failwith "unexpected parameter values"
        )
      )
  do this.AddNamespace(root, [ty])
  
[<assembly:TypeProviderAssembly>]
do ()

  
