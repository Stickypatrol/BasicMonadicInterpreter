//TYPES
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

//type ProgramState = List<char> * 

//actual monads

type State<'a, 's> = 's -> Result<'a,'s>
and Result<'a, 's> =
  | Done of Maybe<'a> * 's
  | Yield of State<'a, 's> * 's
and Maybe<'a> =
  | Success of 'a
  | Error

let rec bind (p:State<'a, 's>) (k:'a -> State<'b, 's>) : State<'b, 's> =
  fun s ->
    match p s with
    | Done(maybe) ->
        match maybe with
        | Error -> Done(Error)
        | Success(a, s') -> k a s'
    | Yield(p', s') -> Yield(bind p' k, s')

let ret x = fun s -> Done(Success(x, s))        

let (>>=) = bind

type StateBuilder() =
  member this.Return(x) = ret x
  member this.ReturnFrom (s:State<'a, 's>) = s
  member this.Bind(p,k) = p >>= k
let st = StateBuilder()

//monadic operators------------------------------------------------------------------

let yield_ = fun s -> Yield((fun s -> Done(Success((), s))), s)

let fail =
  fun s ->
    Done(Error)

let getState =
  fun s ->
    Done(Success(s, s))

let setState x =
  fun s ->
    Done(Success((), x))

let getHead =
  fun s ->
    match s with
    | h::t -> Done(Success(h, t))
    | [] -> Done(Error)

let getEOF =
  fun s ->
    match s with
    | [] -> Done(Success((), []))
    | h::t -> Done(Error)

let (.||) (a:State<'a, 's>) (b:State<'a, 's>) =
  fun s ->
    match a s with
    | Done(maybe) ->
        match maybe with
        | Error -> Done(Error)
        | Success(res, s') -> Done(Success(res, s'))
    | Yield(a', s') ->
        match b s with
        | Done(maybe) ->
            match maybe with
            | Error -> Done(Error)
            | Success(res, s') -> Done(Success(res, s'))
        | Yield(a', s') -> Yield(a', s')

let rec repeated c =
  st{
    let! h = c
    let! t = repeated c
    return h::t
  } .||
  st{
    return []
  }

let rec repeatedAtLeastOnce c =
  st{
    let! h = c
    let! t = repeated c
    return h::t
  }

let Peek (f:State<'a, 's>) =
  st{
    let! olds = getState
    let! res = f
    do! setState olds
    return res
  }

//monadic functions for parsing------------------------------------------------------------
let Whitespace =
  st{
    let! h = getHead
    if h = ' ' || h = '\n' || h = '\r' || h = '\t' then
      return ()
    else
      return! fail
  }

let SkipWhitespace =
  st{
    let! _ = repeated Whitespace
    return ()
  }

let Numeral =
  st{
    let! h = getHead
    if h >= '0' && h <= '9' then
      return h
    else
      return! fail
  }

let ReadNumeral =
  st{
    do! SkipWhitespace
    let! result = repeatedAtLeastOnce Numeral
    return System.Double.Parse(List.fold(fun acc elem -> acc + (elem.ToString())) "" result)
  }

let AddSub =
  st{
    do! SkipWhitespace
    let! h = getHead
    if h = '+' then
      return Plus
    else if h = '-' then
      return Minus
    else
      return! fail
  }

let MultDivide =
  st{
    do! SkipWhitespace
    let! h = getHead
    if h = '*' then
      return Multiply
    else if h = '/' then
      return Divide
    else
      return! fail
  }

let Parens =
  st{
    do! SkipWhitespace
    let! h = getHead
    if h = '(' then
      return Opening
    else if h = ')' then
      return Closing
    else
      return! fail
  }

let PrintState x : State<Unit, 's> =
  fun s ->
    do printfn "%A" x
    do printfn "%A" s
    Done(Success((), s))

//monadic composition functions

let rec FactorW1 (a:State<double, 's>) : State<Factor, 's> =
  fun s ->
    match a s with
    | Yield(a', s') -> Yield(FactorW1 a', s')
    | Done(maybe) ->
        match maybe with
        | Error -> Done(Error)
        | Success(res, s') -> Done(Success(Factor.Wrap(res), s'))


let rec FactorW2 (a:State<PlusMinus, 's>) (b:State<Factor, 's>) =
  fun s ->
    match a s with
    | Yield(a', s') -> Yield(FactorW2 a' b, s')
    | Done(maybe) ->
        match maybe with
        | Error -> Done(Error)
        | Success(resa, s') ->
            match b s' with
            | Yield(b', s'') -> Yield(FactorW2 (ret resa) b', s'')
            | Done(maybe) ->
                match maybe with
                | Error -> Done(Error)
                | Success(resb, s'') -> Done(Success(Factor.Wrap(resa, resb), s''))

let rec FactorW3 a b c =
  fun s ->
    match a s with
    | Yield(a', s') -> Yield(FactorW3 a' b c, s')
    | Done(maybe) ->
        match maybe with
        | Error -> Done(Error)
        | Success(resa, s') ->
            match b s' with
            | Yield(b', s'') -> Yield(FactorW3 (ret resa) b' c, s'')
            | Done(maybe) ->
                match maybe with
                | Error -> Done(Error)
                | Success(resb, s'') ->
                    match c s'' with
                    | Yield(c', s''') -> Yield(FactorW3 (ret resa) (ret resb) c', s''')
                    | Done(maybe) ->
                        match maybe with
                        | Error -> Done(Error)
                        | Success(resc, s''') -> Done(Success(Factor.Wrap(resa, resb, resc), s'''))

let rec TermW1 a =
  fun s ->
    match a s with
    | Yield(a', s') -> Yield(TermW1 a', s')
    | Done(maybe) ->
        match maybe with
        | Error -> Done(Error)
        | Success(res, s') -> Done(Success(Term.Wrap(res), s'))

let rec TermW3 a b c =
  fun s ->
    match a s with
    | Yield(a', s') -> Yield(TermW3 a' b c, s')
    | Done(maybe) ->
        match maybe with
        | Error -> Done(Error)
        | Success(resa, s') ->
            match b s' with
            | Yield(b', s'') -> Yield(TermW3 (ret resa) b' c, s'')
            | Done(maybe) ->
                match maybe with
                | Error -> Done(Error)
                | Success(resb, s'') ->
                    match c s'' with
                    | Yield(c', s''') -> Yield(TermW3 (ret resa) (ret resb) c', s''')
                    | Done(maybe) ->
                        match maybe with
                        | Error -> Done(Error)
                        | Success(resc, s''') -> Done(Success(Term.Wrap(resa, resb, resc), s'''))

let rec ExprW1 a =
  fun s ->
    match a s with
    | Yield(a', s') -> Yield(ExprW1 a', s')
    | Done(maybe) ->
        match maybe with
        | Error -> Done(Error)
        | Success(res, s') -> Done(Success(Expression.Wrap(res), s'))

let rec ExprW3 a b c =
  fun s ->
    match a s with
    | Yield(a', s') -> Yield(ExprW3 a' b c, s')
    | Done(maybe) ->
        match maybe with
        | Error -> Done(Error)
        | Success(resa, s') ->
            match b s' with
            | Yield(b', s'') -> Yield(ExprW3 (ret resa) b' c, s'')
            | Done(maybe) ->
                match maybe with
                | Error -> Done(Error)
                | Success(resb, s'') ->
                    match c s'' with
                    | Yield(c', s''') -> Yield(ExprW3 (ret resa) (ret resb) c', s''')
                    | Done(maybe) ->
                        match maybe with
                        | Error -> Done(Error)
                        | Success(resc, s''') -> Done(Success(Expression.Wrap(resa, resb, resc), s'''))

//PARSER

let rec FactorParser() =
  st{
    do! SkipWhitespace
    let! factor = (FactorW3 Parens (ExprParser()) Parens) .||
                  (FactorW2 AddSub (FactorParser())) .||
                  FactorW1 ReadNumeral
    do! PrintState factor
    return factor
  }

and TermParser() =
  st{
    do! SkipWhitespace
    let! term = (TermW3 (FactorParser()) MultDivide (TermParser())) .||
                (TermW1 (FactorParser()))
    do! PrintState term
    return term
  }

and ExprParser() =
  st{
    do! SkipWhitespace
    let! expr = (ExprW3 (TermParser()) AddSub (ExprParser())) .||
                (ExprW1 (TermParser()))
    do! PrintState expr
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

let rec PrettyPrinter() = 
  st{
    let! p' = ExprParser()
    return p'
  }

let costep c =
  fun s ->
    match c s with
    | Yield(c', s') -> (fun s -> c' s), s'
    | Done(maybe) ->
        match maybe with
        | Error -> (fun s -> Done(Error)), s
        | Success(res, s') -> (fun s -> Done(Success(res, s))), s'

//actual program
let Explode xs =
  [for x in xs do yield x]

let rec Program c s =
  let c', s' = costep c s
  match s' with
  | h::t -> Program c' s'
  | [] -> printfn "Finished parsing, now to evaluate"
          c'
  
  //let evaluated = ExprEval parsestep
  //printfn "%A" (int <| (evaluated %? 1000000007.0))

do ignore <| System.Console.WindowWidth <- 180
do ignore <| System.Console.WindowHeight <- 56
let input = Explode (System.Console.ReadLine())
let finalexpr = Program (ExprParser()) input
