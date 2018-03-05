/// type-level boolean.
[<AutoOpen>]
module FSharp.Dependent.TypeBool

/// Gets a bool value of the given type-level boolean.
let inline boolVal (_: ^X) : bool
  when ^X: (static member eval: ^X -> ^Bool) =
  (^Bool: (static member boolVal: ^Bool -> bool) sing< ^Bool >)

/// if-then-else operation in compile-time.
let inline ifThenElse (_: TypeArg< ^X >) (x, y) : _
  when ^X: (static member eval: ^X -> ^Bool) =
  (^Bool: (static member ifThenElse: _*_*_ -> _) sing< ^Bool >,x,y)

/// type-level true.
[<Struct>]
type True = True with
  static member inline sing (_: True) = True
  static member inline eval True = True
  static member inline ifThenElse (True, x, _) = eval x
  static member inline (==) (True, True) = True
  static member inline boolVal True = true

/// type-level false.
[<Struct>]
type False = False with
  static member inline sing (_: False) = False
  static member inline eval False = False
  static member inline ifThenElse (False, _, y) = eval y
  static member inline (==) (False, False) = True
  static member inline (==) (True, _) = False
  static member inline (==) (_, True) = False
  static member inline boolVal False = false

/// type-level not.
[<Struct>]
type Not<'a> = Not of 'a with
  static member inline eval (Not x) = Not (eval x)
  static member inline ifThenElse (_: Not< ^Expr >, x, y) : _
    when ^Expr: (static member eval: ^Expr -> ^Bool) =
    (^Bool: (static member ifThenElse: _*_*_ -> _) sing< ^Bool >,y,x)
  static member inline sing (_: Not< ^X >) = Not (sing< ^X >)
  static member inline boolVal (Not x) =
    not (boolVal (eval x))

/// type-level and.
[<Struct>]
type And<'a, 'b> = And of 'a * 'b with
  static member inline eval (_: And< ^A, ^B>) : ^Bool
    when ^A: (static member eval: ^A -> ^X)
     and ^B: (static member eval: ^B -> ^Y) =
    (^X: (static member ifThenElse: _*_*_ -> ^Bool) sing< ^X >,sing< ^Y >,False)
  static member inline ifThenElse (_: And< ^A, ^B>, x, y) : _
    when ^A: (static member eval: ^A -> ^X)
     and ^B: (static member eval: ^B -> ^Y)
     and ^X: (static member ifThenElse: ^X * ^Y * False -> ^Bool) =
    (^Bool: (static member ifThenElse: _*_*_ -> _) sing< ^Bool >,x,y)
  static member inline boolVal (And (x, y)) =
    boolVal x && boolVal y

/// type-level or.
[<Struct>]
type Or<'a, 'b> = Or of 'a * 'b with
  static member inline eval (_: Or< ^A, ^B>) : ^Bool
    when ^A: (static member eval: ^A -> ^X)
     and ^B: (static member eval: ^B -> ^Y) =
    (^X: (static member ifThenElse: _*_*_ -> ^Bool) sing< ^X >,True,sing< ^Y >)
  static member inline ifThenElse (_: Or< ^A, ^B>, x, y) : _
    when ^A: (static member eval: ^A -> ^X)
     and ^B: (static member eval: ^B -> ^Y)
     and ^X: (static member ifThenElse: ^X * ^True * ^Y -> ^Bool) =
    (^Bool: (static member ifThenElse: _*_*_ -> _) sing< ^Bool >,x,y)
  static member inline boolVal (Or (x, y)) =
    boolVal x || boolVal y

/// type-level equation.
[<Struct>]
type Eq<'a, 'b> = Eq of 'a * 'b with
  static member inline eval (_: Eq< ^A, ^B>) = Eq(evalSing __< ^A >, evalSing __< ^B >)
  static member inline ifThenElse (_: Eq< ^X, ^Y >, x, y) : _
    when ^X: (static member eval: ^X -> ^X')
     and ^Y: (static member eval: ^Y -> ^Y')
     and (^X' or ^Y'): (static member (==): ^X' * ^Y' -> ^Bool) =
    (^Bool: (static member ifThenElse: _*_*_ -> _) sing< ^Bool >,eval x,eval y)
  static member inline proof (_: Eq< ^X, ^Y >) : ^Z
    when ^X: (static member eval: ^X -> ^Z)
     and ^Y: (static member eval: ^Y -> ^Z) = sing< ^Z >
  static member inline sing (_: Eq< ^A, ^B >) = Eq(sing< ^A >, sing< ^B >)

/// type-level if-then-else.
[<Struct>]
type IfThenElse< '_Bool, '_A, '_B > = IfThenElse of unit with
  static member inline eval (_: IfThenElse< ^Expr, ^A, ^B>) : ^C
    when ^Expr: (static member eval: ^Expr -> ^Bool) =
    (^Bool: (static member ifThenElse: ^Bool * _ * _ -> ^C) (sing< ^Bool >),(evalSing __< ^A >),(evalSing __< ^B >))
  static member inline sing (_: IfThenElse<_,_,_>) = IfThenElse()

/// define a type-level constraint.
let inline constrain< ^X when ^X: (static member eval: ^X -> True) > = ()


