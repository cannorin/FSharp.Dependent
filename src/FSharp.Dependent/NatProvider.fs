namespace ProviderImplementation
open System
open System.IO
open System.Reflection
open FSharp.Core.CompilerServices
open FSharp.Dependent.TypeNats
open Microsoft.FSharp.Control
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Reflection
open Microsoft.FSharp.Compiler.SourceCodeServices
open ProviderImplementation
open ProviderImplementation.ProvidedTypes

module internal ProviderUtils =
  let rec createSucc n terminator =
    if n > 0 then
      let x = createSucc (n-1) terminator
      sprintf "(S %s)" x
    else
      terminator

  let createNat n = createSucc n "Zero"

  let compileAndGet (code: string) =
    let scs = FSharpChecker.Create()
    let ownPath =
      let temp = Path.ChangeExtension(Path.GetTempFileName(), ".dll")
      File.Copy(Assembly.GetExecutingAssembly().Location, temp)
      temp
    let (src, dll) =
      let temp = Path.GetTempFileName()
      (Path.ChangeExtension(temp, ".fsx"), Path.ChangeExtension(temp, ".dll"))
    let code' = "namespace A\nopen FSharp.Dependent\nmodule B =\n  let X = <@@ %%code%% @@>".Replace("%%code%%", code)
    File.WriteAllText(src, code')
    match (scs.CompileToDynamicAssembly([| "fsc.exe"; "-o"; dll; "-r"; ownPath; src |], Some(stdout,stderr), "user") |> Async.RunSynchronously) with
      | [| |], 0, Some a -> 
        let b = a.GetTypes() |> Array.find (fun x -> x.Name = "B")
        let x = b.GetMembers().[0] :?> MethodInfo
        let r = x.Invoke(null, [| |]) :?> Expr
        try
          File.Delete src
          File.Delete dll
          File.Delete ownPath
        finally
          ()
        r
 
      | _ ->
        File.Delete src
        File.Delete dll
        failwith "failed!"
    

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
            let n = ProviderUtils.createNat value |> ProviderUtils.compileAndGet in
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

