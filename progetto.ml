type ide = string;;
type elem = Int of int | String of string;;
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
           Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
           Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
           Letrec of ide * exp * exp |
           
           Estring of string| Set of seq * exp | Insert of exp * exp | Remove of exp * exp | IsEmpty of exp | IsIn of exp * exp | SubSet of exp * exp | Min of exp | Max of exp | 
           ForAll of exp * exp | Exists of exp * exp |Filter of exp * exp | Map of exp * exp 
and seq = Empty  | Singleton of exp * exp | Item of (exp * seq) * exp;; 
(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | String of string| Unbound | FunVal of evFun | RecFunVal of ide * evFun | SetVal of (evT list) * evT
                                                                                                                          
and evFun = ide * exp * evT env;;

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
    "int" -> (match v with
        Int(_) -> true |
        _ -> false) |
    "bool" -> (match v with
        Bool(_) -> true |
        _ -> false) |
    "set" -> (match v with
        SetVal(_) -> true |
        _ -> false)|
    "string" -> (match v with
        String(_) -> true |
        _ -> false)|
    _ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Int(n*u))
  else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Int(n+u))
  else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Int(n-u))
  else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Bool(n=u))
  else failwith("Type error");;

let minus x = if (typecheck "int" x) 
  then (match x with
        Int(n) -> Int(-n))
  else failwith("Type error");;

let iszero x = if (typecheck "int" x)
  then (match x with
        Int(n) -> Bool(n=0))
  else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
        (Bool(b),Bool(e)) -> (Bool(b||e)))
  else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
        (Bool(b),Bool(e)) -> Bool(b&&e))
  else failwith("Type error");;

let non x = if (typecheck "bool" x)
  then (match x with
        Bool(true) -> Bool(false) |
        Bool(false) -> Bool(true))
  else failwith("Type error");;





let rec isin (s: evT list) (x: evT) : bool = match s with
    []->false
  |h::tl-> if (h=x) then true else (isin tl x);;
                                   

let isempty (s:evT list) : bool =  
  match s with
  |[]->true
  |_->false;;
    

let rec subset s1 s2 = match s1,s2 with
  |[],[]->true
  |x::xs,[] -> true
  |x::xs,y::ys -> if (x!=y) then false else subset xs ys;;

let rec min_list  s = match s with 
  |[] -> None
  |y::ys -> match  min_list(ys) with
      None-> Some y
    |Some x -> Some (min y x);;

let rec max_list s = match s with 
  |[] -> None
  |y::ys -> match  max_list(ys) with
      None-> Some y
    |Some x -> Some (max y x);;
                                                                                                                             

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
    Eint n -> Int n |
    Ebool b -> Bool b |
    IsZero a -> iszero (eval a r) |
    Den i -> applyenv r i |
    Eq(a, b) -> eq (eval a r) (eval b r) |
    Prod(a, b) -> prod (eval a r) (eval b r) |
    Sum(a, b) -> sum (eval a r) (eval b r) |
    Diff(a, b) -> diff (eval a r) (eval b r) |
    Minus a -> minus (eval a r) |
    And(a, b) -> et (eval a r) (eval b r) |
    Or(a, b) -> vel (eval a r) (eval b r) |
    Not a -> non (eval a r) |
    Ifthenelse(a, b, c) -> 
      let g = (eval a r) in
      if (typecheck "bool" g) 
      then (if g = Bool(true) then (eval b r) else (eval c r))
      else failwith ("nonboolean guard") |
    Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
    Fun(i, a) -> FunVal(i, a, r) |
    FunCall(f, eArg) -> 
      let fClosure = (eval f r) in
      (match fClosure with
         FunVal(arg, fBody, fDecEnv) -> 
           eval fBody (bind fDecEnv arg (eval eArg r)) |
         RecFunVal(g, (arg, fBody, fDecEnv)) -> 
           let aVal = (eval eArg r) in
           let rEnv = (bind fDecEnv g fClosure) in
           let aEnv = (bind rEnv arg aVal) in
           eval fBody aEnv |
         _ -> failwith("non functional value")) |
    Letrec(f, funDef, letBody) ->
      (match funDef with
         Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
           eval letBody r1 |
         _ -> failwith("non functional def")) 
  
  |Estring(s) -> String(s)
  |Set (e1,e2) -> SetVal (evalSeq e1 eval e2 r) 
  |Insert (e1,e2) -> (match (eval e2 r, eval e1 r) with SetVal (s,tipe), evT x -> if((typecheck "int" x)||(typecheck "string" x)) then 
        if (type (tipe)=type (x)) then
          if (SetVal(isin(s,x),tipe)) then s else x::s
                                                      
        else failwith ("no same type error")
      else failwith ("no correct type of element")
                                                      |_,_ -> failwith("Set error") )
  |Remove (e1,e2) -> (match (eval e2 r , eval e1 r) with 
        SetVal s, evT i -> SetVal (removeSeq s i)
      |_,_-> failwith("Set error") )
  |IsEmpty e1 -> (match (eval e1 r) with
        SetVal s -> SetVal (isempty s)
      |_ -> failwith("Set error"))
  |IsIn (e1,e2) -> (match (eval e2 r , eval e1 r) with
      |SetVal s, evT i -> isin(s,i)
      |_,_ -> failwith("Set error"))
  |SubSet(e1,e2) -> (match (eval e1 r, eval e2 r) with
      | SetVal s1, SetVal s2 -> SetVal (subset(s1,s2))
      |_,_ -> failwith("Set error"))
  |Min e -> (match (eval e r) with 
      |SetVal s1 -> SetVal (min_list(s1))
      |_ -> failwith("Set error"))
  |Max e -> (match (eval e r) with 
      |SetVal s1 -> SetVal (max_list(s1))
      |_ -> failwith("Set error"))
  |ForAll (e1,e2) -> (match (eval e1 r, eval e2 r) with
        FunVal b, SetVal s -> forall(b,s)
      |_,_ -> failwith("Set error"))
  |Exists (e1,e2) -> (match (eval e1 r, eval e2 r) with
        FunVal b, SetVal s -> exists(b,s)
      |_ -> failwith("Set error"))
  |Filter (e1,e2) -> (match (eval e1 r, eval e2 r) with
        FunVal b, SetVal s -> filter(b,s)
      |_ -> failwith("Set error"))

  |Map(e1,e2) -> (match (eval e1 r, eval e2 r) with
        FunVal f, SetVal s -> map(f,s)
      |_ -> failwith("Set error"))
    
    
and let rec evalSeq (s:seq) (t:evT) (r:evT env) : evT list = if((typecheck "int" t)||(typecheck "string" t)) then
        match s with
        |Empty->[],t
        |Singleton(e1,t) -> (eval e1 r),t
        |Item (e1, s1) -> (eval e1 r)::(evalSeq s1 r),t
        |_ -> failwith("set error")              
      else failwith ("no correct type of set")
          
  and let rec removeSeq (s: t list) (i:t) : t list = 
        match s with 
        |[]->[]
        |i1::s1 -> if(i = i1)then s1 else i1::(removeSeq(s1,i))


    and let rec forall (b:exp) (s:t list) (r:evT env) : bool = let b = eval(FunCall(b,r) in 
          if (typecheck "bool" b1) then 
            match s with 
            |[]->true
            |x::xs-> if (b(x)) then forall(b,xs) else false
          else failwith ("not a predicate")

      and let rec exists (b:exp) (s:t list) (r:evT env) : bool = 
            let b = eval(FunCall(b,r) in 
            if (typecheck "bool" b1) then 
              match s with 
              |[]->false
              |x::xs-> if (b(x)) then true else exists(b,xs)
            else failwith ("not a predicate")
        
        and let rec filter (b:exp) (s:t list) (r:evT env) : evT list = let lst = [] in
              let b1 = eval(FunCall(b,r) in 
              if (typecheck "bool" b1) then  
                match s with 
                |[]-> []
                |x::xs-> if (b(x)) then x::lst else filter(b,xs)
              else failwith ("not a predicate")
          
          and let rec map (f:exp) (s:t list) (r:evT env) : t list = 
                let f1 = eval(FunCall(f,r) in 
                match s with
                  [] ->[]
                |x::xs -> (f1 x)::(map f1 xs);;
                                  


               
(* =============================  TESTS  ================= *)

(* basico: no let *)
let env0 = emptyenv Unbound;;

let e1 = FunCall(Fun("y", Sum(Den "y", Eint 1)), Eint 3);;

eval e1 env0;;

let e2 = FunCall(Let("x", Eint 2, Fun("y", Sum(Den "y", Den "x"))), Eint 3);;

eval e2 env0;;

(*========================== Test sui set ==========================*)

let env1 = emptyenv Unbound;;

let s = Empty;;

eval s env1;;

let s1 = Insert (s,Estring "hello");;

eval s1 env1;;

let s2 = Remove (s1,Estring "hello");;

eval s2 env1;;

let s3 = IsIn (s1,Estring "hello");;

eval s3 env1;;

let s4 = Singleton(Eint 1,int);;

eval s4 env1;;

let s5 = Insert(s4,Eint 3);;

eval s5 env1;;

let max = Max(s5);;

eval max env1;;

let min = Min(s5);;

eval min env1;;

let fun0 = Fun("y", Prod(Den "y", Eint 2));; (*Raddoppia i campi del set*)
let map = Map(fun0,s5);;

eval map env1;;

let fun1 = Fun("y", Eq(Den "y", Eint 3));;
let forall = ForAll(fun1, s5);;

eval forall env1;;

let exists = Exists(fun1, s5);;

eval exists env1;;

let filter = Filter(fun1,s5);;

eval filter env1;;

let s6 = Singleton(Eint 1,int);;

eval s6 env1;;

let sub = SubSet(s5,s6);;

eval sub env1;;