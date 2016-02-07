//TYPES
//anna christine speckhart

type Parens =
  | Opening
  | Closing

and PlusMinus =
  | Minus
  | Plus

and MultiDivide =
  | Multiply
  | Divide

and Factor =
  | Number of double
  | Compound of PlusMinus * Factor
  | Parenthesized of Parens*Expression*Parens
  with
    static member Wrap fl =
      Number(fl)
    static member Wrap (pm, f) =
      Compound(pm, f)
    static member Wrap (pa, ex, pb) =
      Parenthesized(pa, ex, pb)

and Term =
  | SingleT of Factor
  | MultipleT of Factor * MultiDivide * Term
  with
    static member Wrap fa =
      SingleT fa
    static member Wrap (f, md, t) =
      MultipleT(f, md, t)

and Expression =
  | Single of Term
  | Multiple of Term * PlusMinus * Expression
  | End
  with
    static member Wrap t =
      Single t
    static member Wrap (t, pm, ex) =
      Multiple(t, pm, ex)

//state definition
type State =
  {
    Text : list<char>
    Tree : Option<Expression>
  }

//actual monads - idea, make a monad that keeps a collection of computations that you can print at any yield
type PauseType =
  | LexerPause
  | ParserPause
  | FinishPause

type StateCoroutine<'a, 's> = 's -> MaybeStep<'a, 's>
and MaybeStep<'a, 's> =
  | Done of 'a*'s
  | Pause of PauseType*StateCoroutine<'a, 's> * 's
  | Error of List<string>*'s

//monad implementation
and CoroutineBuilder() =
  member this.Return(x) = fun s -> Done(x, s)
  member this.ReturnFrom(s:StateCoroutine<'a, 's>) = s
  member this.Bind(p:StateCoroutine<'a, 's>,k:'a -> StateCoroutine<'b, 's>) : StateCoroutine<'b, 's> =
    fun s ->
      match p s with
      | Done(a, s') -> k a s' //continue with next monadic operation
      | Pause(pt, p', s') -> Pause(pt, this.Bind(p', k), s') //pause until you are provided with another state
      | Error(errormsg, s) -> Error(errormsg, s) //propagate the error
let co = CoroutineBuilder()

//monadic operators------------------------------------------------------------------

let pause_ pt = fun s -> Pause(pt, (fun s -> Done((), s)), s)
//time to start modifying these to fit the new monad definition
let fail msg =
  fun s ->
    Error([msg], s)

let getState =
  fun s ->
    Done(s, s)

let setState x =
  fun s ->
    Done((), x)

let getHead =
  fun (s:State) ->
    match s.Text with
    | h::t -> Done(h, {s with Text = t})
    | [] -> Error(["couldn't get ANY head"], s)

let getEOF =
  fun s ->
    match s with
    | [] -> Done((), s)
    | h::t -> Error(["couldn't get EOF"], s)

let rec (.||) (x:StateCoroutine<'a, 's>) (y:StateCoroutine<'a, 's>) =
  fun s ->
    match x s with
    | Done(a, s') ->
        Done(a, s')
    | Error(errormsg1, s')->
        match y s with
        | Done(a, s') ->  //printfn "Result = %A" a
                          Done(a, s')
        | Error(errormsg2, s') -> Error(List.append errormsg1 errormsg2, s')
        | Pause(pt, y', s') -> Pause(pt, y', s')
    | Pause(pt, x', s') ->
        Pause(pt, (.||) x' y, s')

let rec repeated c =
  co{
    let! h = c
    let! t = repeated c
    return h::t
  } .||
  co{
    return []
  }

let rec repeatedAtLeastOnce c =
  co{
    let! h = c
    let! t = repeated c
    return h::t
  }

let Peek (f:StateCoroutine<'a, 's>) =
  co{
    let! olds = getState
    let! res = f
    do! setState olds
    return res
  }

//monadic functions for parsing------------------------------------------------------------
let Whitespace =
  co{
    let! h = getHead
    if h = ' ' || h = '\n' || h = '\r' || h = '\t' then
      return ()
    else
      return! fail "expected whitespace"
  }

let SkipWhitespace =
  co{
    let! _ = repeated Whitespace
    return ()
  }

let Numeral =
  co{
    let! h = getHead
    if h >= '0' && h <= '9' then
      return h
    else
      return! fail "expected numeral"
  }

let ReadNumeral =
  co{
    do! SkipWhitespace
    let! result = repeatedAtLeastOnce Numeral
    return System.Double.Parse(List.fold(fun acc elem -> acc + (elem.ToString())) "" result)
  }

let AddSub =
  co{
    do! SkipWhitespace
    let! h = getHead
    if h = '+' then
      return Plus
    else if h = '-' then
      return Minus
    else
      return! fail "expected addition or subtraction"
  }

let MultDivide =
  co{
    do! SkipWhitespace
    let! h = getHead
    if h = '*' then
      return Multiply
    else if h = '/' then
      return Divide
    else
      return! fail "expected multiply or divide"
  }

let Parens =
  co{
    do! SkipWhitespace
    let! h = getHead
    if h = '(' then
      return Opening
    else if h = ')' then
      return Closing
    else
      return! fail "expected parenthesis"
  }

let PrintState : StateCoroutine<Unit, 's> =
  fun s ->
    do printfn "%A" s
    Done((), s)

//monadic composition functions

let rec FactorW1 (x:StateCoroutine<double, 's>) : StateCoroutine<Factor, 's> =
  fun s ->
    match x s with
    | Pause(pt, x', s') -> Pause(pt, FactorW1 x', s')
    | Error(errormsg, s') -> Error(errormsg, s')
    | Done(resx, s') -> Done(Factor.Wrap(resx), s')


let rec FactorW2 (x:StateCoroutine<PlusMinus, 's>) (y:StateCoroutine<Factor, 's>) =
  fun s ->
    match x s with
    | Pause(pt, x', s') -> Pause(pt, FactorW2 x' y, s')
    | Error(errormsg, s') -> Error(errormsg, s')
    | Done(resx, s') ->
        match y s' with
        | Pause(pt, y', s'') -> Pause(pt, FactorW2 (co{return resx}) y', s'')
        | Error(errormsg, s') -> Error(errormsg, s')
        | Done(resy, s'') -> Done(Factor.Wrap(resx, resy), s'')

let rec FactorW3 x y z =
  fun s ->
    match x s with
    | Pause(pt, x', s') -> Pause(pt, FactorW3 x' y z, s')
    | Error(errormsg, s') -> Error(errormsg, s')
    | Done(resx, s') ->
        match y s' with
        | Pause(pt, y', s'') -> Pause(pt, FactorW3 (co{return resx}) y' z, s'')
        | Error(errormsg, s'') -> Error(errormsg, s'')
        | Done(resy, s'') -> 
            match z s'' with
            | Pause(pt, z', s''') -> Pause(pt, FactorW3 (co{return resx}) (co{return resy}) z', s''')
            | Error(errormsg, s''') -> Error(errormsg, s''')
            | Done(resz, s''') -> Done(Factor.Wrap(resx, resy, resz), s''')

let rec TermW1 (x:StateCoroutine<Factor, 's>) : StateCoroutine<Term, 's> =
  fun s ->
    match x s with
    | Pause(pt, x', s') -> Pause(pt, TermW1 x', s')
    | Error(errormsg, s') -> Error(errormsg, s')
    | Done(resx, s') -> Done(Term.Wrap(resx), s')

let rec TermW3 x y z =
  fun s ->
    match x s with
    | Pause(pt, x', s') -> Pause(pt, TermW3 x' y z, s')
    | Error(errormsg, s') -> Error(errormsg, s')
    | Done(resx, s') ->
        match y s' with
        | Pause(pt, y', s'') -> Pause(pt, TermW3 (co{return resx}) y' z, s'')
        | Error(errormsg, s'') -> Error(errormsg, s'')
        | Done(resy, s'') -> 
            match z s'' with
            | Pause(pt, z', s''') -> Pause(pt, TermW3 (co{return resx}) (co{return resy}) z', s''')
            | Error(errormsg, s''') -> Error(errormsg, s''')
            | Done(resz, s''') -> Done(Term.Wrap(resx, resy, resz), s''')


let rec ExprW1 (x:StateCoroutine<Term, 's>) : StateCoroutine<Expression, 's> =
  fun s ->
    match x s with
    | Pause(pt, x', s') -> Pause(pt, ExprW1 x', s')
    | Error(errormsg, s') -> Error(errormsg, s')
    | Done(resx, s') -> Done(Expression.Wrap(resx), s')

let rec ExprW3 x y z =
  fun s ->
    match x s with
    | Pause(pt, x', s') -> Pause(pt, ExprW3 x' y z, s')
    | Error(errormsg, s') -> Error(errormsg, s')
    | Done(resx, s') ->
        match y s' with
        | Pause(pt, y', s'') -> Pause(pt, ExprW3 (co{return resx}) y' z, s'')
        | Error(errormsg, s'') -> Error(errormsg, s'')
        | Done(resy, s'') -> 
            match z s'' with
            | Pause(pt, z', s''') -> Pause(pt, ExprW3 (co{return resx}) (co{return resy}) z', s''')
            | Error(errormsg, s''') -> Error(errormsg, s''')
            | Done(resz, s''') -> Done(Expression.Wrap(resx, resy, resz), s''')

//PARSER

let rec FactorParser() =
  co{
    do! SkipWhitespace
    do! pause_ ParserPause
    let! factor = (FactorW3 Parens (ExprParser()) Parens) .||
                  (FactorW2 AddSub (FactorParser())) .||
                  FactorW1 ReadNumeral
    return factor
  }

and TermParser() =
  co{
    do! SkipWhitespace
    do! pause_ ParserPause
    let! term = (TermW3 (FactorParser()) MultDivide (TermParser())) .||
                (TermW1 (FactorParser()))
    return term
  }

and ExprParser() =
  co{
    do! SkipWhitespace
    do! pause_ ParserPause
    let! expr = (ExprW3 (TermParser()) AddSub (ExprParser())) .||
                (ExprW1 (TermParser()))
    do! SkipWhitespace
    return expr
  }

//EVALUATOR

let (%?) a b =
  (a % b + b) % b

let rec FactorEval factor =
  match factor with
  | Number(num) -> num
  | Compound(op,factor') ->
      match op with
      | Minus -> - FactorEval factor'
      | Plus -> FactorEval factor'
  | Parenthesized(_, expr', _) -> ExprEval expr'

and TermEval term =
  match term with
  | SingleT(factor) -> FactorEval factor
  | MultipleT(factor, op, term') ->
      match op with
      | Multiply -> (FactorEval factor) * (TermEval term')
      | Divide -> (FactorEval factor) / (TermEval term')

and ExprEval expr =
  match expr with
  | Single term -> TermEval term
  | Multiple(term, op, expr') ->
      match op with
      | Plus -> (TermEval term) % 1000000007.0 + (ExprEval expr')
      | Minus -> (TermEval term) % 1000000007.0 - (ExprEval expr')
  | End -> 0.0

let rec costep (c:StateCoroutine<Expression, State>) (pauses:List<PauseType>) =
  fun s ->
    match c s with
    | Done(a, s') -> (fun s -> Done(a, s)), s'
    | Error(errormsg, s') -> (fun s -> Done(End, s)), s'
    | Pause(pt, c', s') ->
        if List.exists(fun listpt -> listpt = pt) pauses then
          (fun s -> c' s), s'
        else
          costep c' pauses s'

//actual program
let Explode xs =
  [for x in xs do yield x]

let rec Program (c:StateCoroutine<Expression, State>) (s:State) pauses =
  let c', s' = costep c pauses s
  match s'.Text with
  | h::t -> printfn "Head:'%A' Tail:'%A'" h t
            System.Console.ReadLine()
            Program c' s' pauses
  | [] -> printfn "Finished parsing, now to evaluate"
          c'

let pauses = [LexerPause;ParserPause] //which kinds of pauses(or yields) to actually pause the entire coroutine at
do ignore <| System.Console.WindowWidth <- 180
do ignore <| System.Console.WindowHeight <- 56
let input = {Text = Explode (System.Console.ReadLine()); Tree = None}
let finalexpr = Program (ExprParser()) input pauses