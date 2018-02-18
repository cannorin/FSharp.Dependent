# Using Constraints and Ranged Naturals

There are several constructs which are useful to work with type-level naturals.

## `Constraint.LTE`
  
Helper type function to constrain a certain type-level natural `^NatL` to be less than the specified nat `^NatR` or equal to.

### Description

Although being a bit verbose, using this type is far more performance-wise than just doing ```m - n |> ignore;```
Use this to constrain argument types. If you want to make the return value less than a certain value or equal to, use `RuntimeNat.LTE` instead.

### Example

    let inline pleaseGiveMeLessThan (limit: S< ^NatLimit >) (x: ^NatX) =
      Constraint.LTE< ^NatX, ^NatLimit, _ >;
      printfn "I'm happy with it."
     
    pleaseGiveMeLessThan (S (S Zero)) Zero

### Warning

Place type variables on the left side!
If you put a known type-level natural on the left side, F# typer will constrain the right side to be the same as the left side.

    let inline wrongLT4 (x: ^Nat) =
      Constraint.GTE< S<S<S<Z>>>, ^Nat, _>;
      printfn "less than 4"
    // warning FS0064: ...
    // val inline wrongLT4 : x:S<S<S<Z>>> -> unit

    let inline rightLT4 (x: ^Nat) =
      Constraint.LTE< ^Nat, S<S<S<Z>>>, _>;
      printfn "less than 4"
    // val inline rightLT4:
    //   x: ^Nat -> unit when  ^Nat : (static member ( - ) : S<S<S<Z>>> *  ^Nat ->  ^a)

## `Constraint.LTETerm`

Short-hand alternative to `Constraint.LTE` that takes term arguments instead of type arguments.
See `Constraint.LTE` for details.

### Example

The formar example can be re-written as:

    let inline pleaseGiveMeLessThan limit x =
      Constraint.LTETerm(x, pred limit);
      printfn "I'm happy with it."


## `Constraint.GTE`

Helper type function to constrain a certain type-level natural ^NatL to be greater than the specified nat ^NatR or equal to.

### Description

Although being a bit verbose, using this type is far more performance-wise than just doing ```m - n |> ignore;```
Use this to constrain argument types. If you want to make the return value greater than a certain value or equal to, use `RuntimeNat.GTE` instead.

### Example

    let inline pleaseGiveMeMoreThan (limit: ^NatLimit) (x: ^NatX) =
      Constraint.GTE< ^NatX, S< ^NatLimit >, _ >;
      printfn "I'm happy with it."
    
    pleaseGiveMeMoreThan (S Zero) (S (S Zero))

### Warning

Place type variables on the left side!
If you put a known type-level natural on the left side, F# typer will constrain the right side to be the same as the left side.

    let inline wrongLT4 (x: ^Nat) =
      Constraint.GTE< S<S<S<Z>>>, ^Nat, _>;
      printfn "less than 4"
    // warning FS0064: ...
    // val inline wrongLT4 : x:S<S<S<Z>>> -> unit
    
    let inline rightLT4 (x: ^Nat) =
      Constraint.LTE< ^Nat, S<S<S<Z>>>, _>;
      printfn "less than 4"
    // val inline rightLT4:
    //   x: ^Nat -> unit when  ^Nat : (static member ( - ) : S<S<S<Z>>> *  ^Nat ->  ^a)


## `Constraint.GTETerm`

Short-hand alternative to `Constraint.GTE` that takes term arguments instead of type arguments.
See `Constraint.GTE` for details.

### Example

The formar example can be re-written as:

    let inline pleaseGiveMeMoreThan limit x =
      Constraint.GTETerm(x, succ limit);
      printfn "I'm happy with it."

### `RuntimeNat.LTE`

Creates upper-bounded type-level natural whose term-level value is unknown at compile-time.

### Description

This construct is useful when you want to make sure that the return value is unknown at compile-time, but always less than a certain value or equal.
Use this to constrain return types. If you want to make arguments less than a certain value, use `Constraint.LTE` instead.

### Example

    let inline randomLessThan (n: S< ^Nat >) =
      let rand = System.Random().Next(0, natVal n - 1)
      rand |> RuntimeNat.LTE <| pred n

### Warning

This construct is UNSAFE and will throw an InvalidArgumentException if the given value is larger than the specified upper limit.


## `RuntimeNat.GTE`

Creates lower-bounded type-level natural whose term-level value is unknown at compile-time.

### Description

This construct is useful when you want to make sure that the return value is unknown at compile-time, but always greater than a certain value or equal.
Use this to constrain return types. If you want to make arguments greater than a certain value, use `Constraint.GTE` instead.

### Example

    let inline randomMoreThan (n: ^Nat) =
      let rand = System.Random().Next(natVal n + 1, System.Int32.MaxValue)
      rand |> RuntimeNat.GTE <| S n

### Warning

This construct is UNSAFE and will throw an InvalidArgumentException if the given value is larger than the specified upper limit.

