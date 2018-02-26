namespace FSharp.Dependent.NatProvider
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

module internal ProviderUtils =
  let private S = typedefof<S<Z>>.GetGenericTypeDefinition()
  let private Z = typeof<Z>
  let mutable private memot = Map.empty |> Map.add 0 Z
  let rec createNatType n =
    match memot |> Map.tryFind n with
      | Some x -> x
      | None ->
        if n > 0 then
          let x = S.MakeGenericType(createNatType(n-1))
          memot <- memot |> Map.add n x
          x
        else
          Z

  let mutable private memov = Map.empty |> Map.add 0 (<@@ Zero @@>)
  let rec createNatValue n =
    match memov |> Map.tryFind n with
      | Some x -> x
      | None ->
        if n > 0 then
          let uci = createNatType n |> FSharpType.GetUnionCases
                                    |> Seq.head
          let x = Expr.NewUnionCase(uci, [createNatValue(n-1)])
          memov <- memov |> Map.add n x
          x
        else
          <@@ Zero @@>    

[<TypeProvider>]
type NatProvider (cfg) as this =
  inherit TypeProviderForNamespaces(cfg)
  let thisAsm = Assembly.GetExecutingAssembly()
  let root = "FSharp.Dependent"
  let baseTy = typeof<obj>
  let prm = [ProvidedStaticParameter("value", typeof<int>)]
  let ty = ProvidedTypeDefinition(thisAsm, root, "Nat", Some baseTy, isErased = true)
  do ty.DefineStaticParameters(
      parameters = prm,
      instantiationFunction = (fun tyName prmValues ->
        match prmValues with
          | [| :? int as value |] ->
            if value < 0 then
              failwith "value is negative"
            ty.AddXmlDoc "Type-level naturals."
            let n = ProviderUtils.createNatValue value in
            let ty = ProvidedTypeDefinition(thisAsm, root, tyName, baseType = Some n.Type, isErased = true)
            let valuet = ProvidedProperty("value", n.Type, isStatic = true, getterCode = fun _ -> Expr.Coerce(n, n.Type))
            valuet.AddXmlDoc "Type-level natural number."
            ty.AddMember valuet
            ty
          | _ -> failwith "unexpected parameter values"
        )
      )
  do this.AddNamespace(root, [ty])
  
[<assembly:TypeProviderAssembly>]
do ()

