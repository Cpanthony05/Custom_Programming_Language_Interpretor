
inductive Tip where
  | Int : Tip
  | Bool : Tip
  | List : Tip -> Tip
  deriving Repr, BEq, Inhabited

open Tip


mutual
inductive AExp where
  | var : String -> AExp
  | num : Int -> AExp
  | adunare : AExp -> AExp -> AExp
  | scadere : AExp -> AExp -> AExp
  | inmultire : AExp -> AExp -> AExp
  | impartire : AExp -> AExp -> AExp
  | modulo : AExp -> AExp -> AExp
  | head : LExp -> AExp
  | length : LExp -> AExp
  | nth : LExp -> AExp -> AExp
  deriving Inhabited


inductive LExp where
  | empty : Tip -> LExp
  | cons : AExp -> LExp -> LExp
  | var : String -> LExp
  | append : LExp -> LExp -> LExp
  deriving Inhabited
end

open AExp
open LExp

instance : OfNat AExp n where
  ofNat := AExp.num n
instance : Coe String AExp where
  coe := AExp.var

infixl : 20 " +' " => adunare
infixl : 20 " -' " => scadere
infixl : 25 " *' " => inmultire
infixl : 25 " /' " => impartire
infixl : 25 " %' " => modulo


inductive BExp where
  | T : BExp
  | F : BExp
  | var : String -> BExp
  | egalitate : AExp -> AExp -> BExp
  | mai_mic : AExp -> AExp -> BExp
  | mai_mic_sau_egal : AExp -> AExp -> BExp
  | negatie : BExp -> BExp
  | conjunctie : BExp -> BExp -> BExp
  | disjunctie : BExp -> BExp -> BExp
  | isEmpty : LExp -> BExp
  deriving Inhabited

open BExp

infixl : 10 " ==' " => egalitate
infixl : 10 " <' " => mai_mic
infixl : 10 " <=' " => mai_mic_sau_egal
prefix : 5 " !' " => negatie
infixl : 3 " and' " => conjunctie
infixl : 3 " or' " => disjunctie

instance : Coe String BExp where
  coe := BExp.var

inductive Com where
  | skip : Com
  | declaratie : String → Tip → AExp → Com
  | declaratie_bool : String → BExp → Com
  | declaratie_list : String → Tip → LExp → Com
  | atribuire : String → AExp → Com
  | atribuire_bool : String → BExp → Com
  | atribuire_list : String → LExp → Com
  | secventa : Com → Com → Com
  | while : BExp → Com → Com
  | ite : BExp → Com → Com → Com
  | for : Com → BExp → Com → Com → Com
  | bloc : Com → Com
  | declaratie_functie : String → List (String × Tip) → Tip → Com → Com
  | apel_functie : String → List AExp → Com
  | apel_functie_bool : String → List AExp → Com
  | return : String → Com
  | pop : String → Com
  deriving Inhabited

open Com

notation:2 var:2 " ::= " a:3 => atribuire var a
notation:2 var:2 " ::=b " b:3 => atribuire_bool var b
notation:2 var:2 " ::=l " l:3 => atribuire_list var l
notation:2 var:2 " :::= " tip:3 ", " a:3 => declaratie var tip a
notation:2 var:2 " :::=b " b:3 => declaratie_bool var b
notation:2 var:2 " :::=l " tip:3 ", " l:3 => declaratie_list var tip l
notation "{" c "}" => Com.bloc c
infixr:1 " ;; " => secventa


inductive Value where
  | intVal : Int -> Value
  | boolVal : Bool -> Value
  | listVal : List Int -> Value
  deriving Repr, Inhabited

def Env : Type := String → Value
def NEDECLARAT_VAL : Value := Value.intVal (-2147483649)

def update (sigma : Env) (var : String) (val : Value) : Env :=
  fun x => if (x == var) then val else sigma x


def TipEnv : Type := String → Option Tip
def tipenv_default : TipEnv := fun _ => none
def updateTip (T : TipEnv) (var : String) (tip : Tip) : TipEnv :=
  fun x => if (x == var) then some tip else T x


inductive EvalError where
  | DivisionByZero : EvalError
  | TypeMismatch : String -> EvalError
  | UndeclaredVariable : String -> EvalError
  | VariableAlreadyDeclared : String -> EvalError
  | FunctionAlreadyDeclared : String -> EvalError
  | NoCondition : EvalError
  | UndeclaredFunction : String -> EvalError
  | WrongType : String -> Tip -> Tip -> EvalError
  | EmptyList : EvalError
  | IndexOutOfBounds : EvalError
  deriving Repr, Inhabited


mutual

partial def typeCheckLExp (l : LExp) (tipenv : TipEnv) : Except EvalError Tip :=
  match l with
  | LExp.empty t => Except.ok (Tip.List t)
  | LExp.cons a l' =>
      match typeCheckAExp a tipenv with
      | Except.error e => Except.error e
      | Except.ok Tip.Int =>
          match typeCheckLExp l' tipenv with
          | Except.error e => Except.error e
          | Except.ok (Tip.List Tip.Int) => Except.ok (Tip.List Tip.Int)
          | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected List Int, got {repr t}")
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in list, got {repr t}")
  | LExp.var x =>
      match tipenv x with
      | none => Except.error (EvalError.UndeclaredVariable x)
      | some t@(Tip.List _) => Except.ok t
      | some t => Except.error (EvalError.TypeMismatch s!"Expected List type for {x}, got {repr t}")
  | LExp.append l1 l2 =>
      match typeCheckLExp l1 tipenv with
      | Except.error e => Except.error e
      | Except.ok (Tip.List t1) =>
          match typeCheckLExp l2 tipenv with
          | Except.error e => Except.error e
          | Except.ok (Tip.List t2) =>
              if t1 == t2 then
                Except.ok (Tip.List t1)
              else
                Except.error (EvalError.TypeMismatch "Cannot append lists of different types")
          | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected List in append, got {repr t}")
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected List in append, got {repr t}")


partial def typeCheckAExp (a : AExp) (tipenv : TipEnv) : Except EvalError Tip :=
  match a with
  | num _ => Except.ok Tip.Int
  | AExp.var x =>
      match tipenv x with
      | none => Except.error (EvalError.UndeclaredVariable x)
      | some t =>
          if t == Tip.Int then
            Except.ok Tip.Int
          else
            Except.error (EvalError.WrongType x Tip.Int t)
  | adunare a1 a2 =>
      match typeCheckAExp a1 tipenv with
      | Except.error e => Except.error e
      | Except.ok Tip.Int =>
          match typeCheckAExp a2 tipenv with
          | Except.error e => Except.error e
          | Except.ok Tip.Int => Except.ok Tip.Int
          | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in addition, got {repr t}")
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in addition, got {repr t}")
  | scadere a1 a2 =>
      match typeCheckAExp a1 tipenv with
      | Except.error e => Except.error e
      | Except.ok Tip.Int =>
          match typeCheckAExp a2 tipenv with
          | Except.error e => Except.error e
          | Except.ok Tip.Int => Except.ok Tip.Int
          | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in subtraction, got {repr t}")
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in subtraction, got {repr t}")
  | inmultire a1 a2 =>
      match typeCheckAExp a1 tipenv with
      | Except.error e => Except.error e
      | Except.ok Tip.Int =>
          match typeCheckAExp a2 tipenv with
          | Except.error e => Except.error e
          | Except.ok Tip.Int => Except.ok Tip.Int
          | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in multiplication, got {repr t}")
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in multiplication, got {repr t}")
  | impartire a1 a2 =>
      match typeCheckAExp a1 tipenv with
      | Except.error e => Except.error e
      | Except.ok Tip.Int =>
          match typeCheckAExp a2 tipenv with
          | Except.error e => Except.error e
          | Except.ok Tip.Int => Except.ok Tip.Int
          | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in division, got {repr t}")
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in division, got {repr t}")
  | modulo a1 a2 =>
      match typeCheckAExp a1 tipenv with
      | Except.error e => Except.error e
      | Except.ok Tip.Int =>
          match typeCheckAExp a2 tipenv with
          | Except.error e => Except.error e
          | Except.ok Tip.Int => Except.ok Tip.Int
          | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in modulo, got {repr t}")
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in modulo, got {repr t}")
  | AExp.head l =>
      match typeCheckLExp l tipenv with
      | Except.error e => Except.error e
      | Except.ok (Tip.List Tip.Int) => Except.ok Tip.Int
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected List Int for head, got {repr t}")
  | AExp.length l =>
      match typeCheckLExp l tipenv with
      | Except.error e => Except.error e
      | Except.ok (Tip.List _) => Except.ok Tip.Int
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected List for length, got {repr t}")
  | AExp.nth l idx =>
      match typeCheckLExp l tipenv with
      | Except.error e => Except.error e
      | Except.ok (Tip.List Tip.Int) =>
          match typeCheckAExp idx tipenv with
          | Except.error e => Except.error e
          | Except.ok Tip.Int => Except.ok Tip.Int
          | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int for index, got {repr t}")
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected List Int for nth, got {repr t}")
end


partial def typeCheckBExp (b : BExp) (tipenv : TipEnv) : Except EvalError Tip :=
  match b with
  | T => Except.ok Tip.Bool
  | F => Except.ok Tip.Bool
  | BExp.var x =>
      match tipenv x with
      | none => Except.error (EvalError.UndeclaredVariable x)
      | some Tip.Bool => Except.ok Tip.Bool
      | some t => Except.error (EvalError.WrongType x Tip.Bool t)
  | egalitate a1 a2 =>
      match typeCheckAExp a1 tipenv with
      | Except.error e => Except.error e
      | Except.ok Tip.Int =>
          match typeCheckAExp a2 tipenv with
          | Except.error e => Except.error e
          | Except.ok Tip.Int => Except.ok Tip.Bool
          | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in equality, got {repr t}")
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in equality, got {repr t}")
  | mai_mic a1 a2 =>
      match typeCheckAExp a1 tipenv with
      | Except.error e => Except.error e
      | Except.ok Tip.Int =>
          match typeCheckAExp a2 tipenv with
          | Except.error e => Except.error e
          | Except.ok Tip.Int => Except.ok Tip.Bool
          | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in comparison, got {repr t}")
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in comparison, got {repr t}")
  | mai_mic_sau_egal a1 a2 =>
      match typeCheckAExp a1 tipenv with
      | Except.error e => Except.error e
      | Except.ok Tip.Int =>
          match typeCheckAExp a2 tipenv with
          | Except.error e => Except.error e
          | Except.ok Tip.Int => Except.ok Tip.Bool
          | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in comparison, got {repr t}")
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Int in comparison, got {repr t}")
  | negatie b1 =>
      match typeCheckBExp b1 tipenv with
      | Except.error e => Except.error e
      | Except.ok Tip.Bool => Except.ok Tip.Bool
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Bool in negation, got {repr t}")
  | conjunctie b1 b2 =>
      match typeCheckBExp b1 tipenv with
      | Except.error e => Except.error e
      | Except.ok Tip.Bool =>
          match typeCheckBExp b2 tipenv with
          | Except.error e => Except.error e
          | Except.ok Tip.Bool => Except.ok Tip.Bool
          | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Bool in conjunction, got {repr t}")
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Bool in conjunction, got {repr t}")
  | disjunctie b1 b2 =>
      match typeCheckBExp b1 tipenv with
      | Except.error e => Except.error e
      | Except.ok Tip.Bool =>
          match typeCheckBExp b2 tipenv with
          | Except.error e => Except.error e
          | Except.ok Tip.Bool => Except.ok Tip.Bool
          | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Bool in disjunction, got {repr t}")
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected Bool in disjunction, got {repr t}")
  | BExp.isEmpty l =>
      match typeCheckLExp l tipenv with
      | Except.error e => Except.error e
      | Except.ok (Tip.List _) => Except.ok Tip.Bool
      | Except.ok t => Except.error (EvalError.TypeMismatch s!"Expected List for isEmpty, got {repr t}")


mutual

partial def leval (l : LExp) (sigma : Env) : Except EvalError (List Int) :=
  match l with
  | LExp.empty _ => Except.ok []
  | LExp.cons a l' =>
      match aeval a sigma with
      | Except.error e => Except.error e
      | Except.ok v =>
          match leval l' sigma with
          | Except.error e => Except.error e
          | Except.ok vs => Except.ok (v :: vs)
  | LExp.var x =>
      match sigma x with
      | Value.listVal lst => Except.ok lst
      | Value.intVal i =>
          if i == -2147483649 then
            Except.error (EvalError.UndeclaredVariable x)
          else
            Except.error (EvalError.TypeMismatch s!"Expected list for {x}")
      | _ => Except.error (EvalError.TypeMismatch s!"Expected list for {x}")
  | LExp.append l1 l2 =>
      match leval l1 sigma with
      | Except.error e => Except.error e
      | Except.ok v1 =>
          match leval l2 sigma with
          | Except.error e => Except.error e
          | Except.ok v2 => Except.ok (v1 ++ v2)





partial def aeval (a : AExp) (sigma : Env) : Except EvalError Int :=
  match a with
  | num i => Except.ok i
  | AExp.var x =>
      match sigma x with
      | Value.intVal v =>
          if v == -2147483649 then
            Except.error (EvalError.UndeclaredVariable x)
          else
            Except.ok v
      | _ => Except.error (EvalError.TypeMismatch s!"Expected Int for {x}")
  | adunare a1 a2 =>
      match aeval a1 sigma with
      | Except.error e => Except.error e
      | Except.ok v1 =>
          match aeval a2 sigma with
          | Except.error e => Except.error e
          | Except.ok v2 => Except.ok (v1 + v2)
  | scadere a1 a2 =>
      match aeval a1 sigma with
      | Except.error e => Except.error e
      | Except.ok v1 =>
          match aeval a2 sigma with
          | Except.error e => Except.error e
          | Except.ok v2 => Except.ok (v1 - v2)
  | inmultire a1 a2 =>
      match aeval a1 sigma with
      | Except.error e => Except.error e
      | Except.ok v1 =>
          match aeval a2 sigma with
          | Except.error e => Except.error e
          | Except.ok v2 => Except.ok (v1 * v2)
  | impartire a1 a2 =>
      match aeval a1 sigma with
      | Except.error e => Except.error e
      | Except.ok v1 =>
          match aeval a2 sigma with
          | Except.error e => Except.error e
          | Except.ok v2 =>
              if v2 == 0 then
                Except.error EvalError.DivisionByZero
              else
                Except.ok (v1 / v2)
  | modulo a1 a2 =>
      match aeval a1 sigma with
      | Except.error e => Except.error e
      | Except.ok v1 =>
          match aeval a2 sigma with
          | Except.error e => Except.error e
          | Except.ok v2 =>
              if v2 == 0 then
                Except.error EvalError.DivisionByZero
              else
                Except.ok (v1 % v2)
  | AExp.head l =>
      match leval l sigma with
      | Except.error e => Except.error e
      | Except.ok [] => Except.error EvalError.EmptyList
      | Except.ok (h :: _) => Except.ok h
  | AExp.length l =>
      match leval l sigma with
      | Except.error e => Except.error e
      | Except.ok lst => Except.ok lst.length
  | AExp.nth l idx =>
    match leval l sigma with
    | Except.error e => Except.error e
    | Except.ok lst =>
        match aeval idx sigma with
        | Except.error e => Except.error e
        | Except.ok i =>
            if i < 0 || i >= lst.length then
              Except.error EvalError.IndexOutOfBounds
            else
              let rec getNth (lst : List Int) (n : Nat) : Int :=
                match lst, n with
                | h :: _, 0 => h
                | _ :: t, n' + 1 => getNth t n'
                | [], _ => 0
              Except.ok (getNth lst i.toNat)
end


partial def beval (b : BExp) (sigma : Env) : Except EvalError Bool :=
  match b with
  | T => Except.ok true
  | F => Except.ok false
   | BExp.var x =>
      match sigma x with
      | Value.boolVal v => Except.ok v
      | Value.intVal i =>
          if i == -2147483649 then
            Except.error (EvalError.UndeclaredVariable x)
          else if i == 1 then
            Except.ok true
          else if i == 0 then
            Except.ok false
          else
            Except.error (EvalError.TypeMismatch s!"Expected Bool for {x}, got Int")
      | _ => Except.error (EvalError.TypeMismatch s!"Expected Bool for {x}")
  | egalitate a1 a2 =>
      match aeval a1 sigma with
      | Except.error e => Except.error e
      | Except.ok v1 =>
          match aeval a2 sigma with
          | Except.error e => Except.error e
          | Except.ok v2 => Except.ok (v1 == v2)
  | mai_mic a1 a2 =>
      match aeval a1 sigma with
      | Except.error e => Except.error e
      | Except.ok v1 =>
          match aeval a2 sigma with
          | Except.error e => Except.error e
          | Except.ok v2 => Except.ok (v1 < v2)
  | mai_mic_sau_egal a1 a2 =>
      match aeval a1 sigma with
      | Except.error e => Except.error e
      | Except.ok v1 =>
          match aeval a2 sigma with
          | Except.error e => Except.error e
          | Except.ok v2 => Except.ok (v1 <= v2)
  | negatie b1 =>
      match beval b1 sigma with
      | Except.error e => Except.error e
      | Except.ok v => Except.ok (!v)
  | conjunctie b1 b2 =>
      match beval b1 sigma with
      | Except.error e => Except.error e
      | Except.ok v1 =>
          if v1 then
            beval b2 sigma
          else
            Except.ok false
  | disjunctie b1 b2 =>
      match beval b1 sigma with
      | Except.error e => Except.error e
      | Except.ok v1 =>
          if v1 then
            Except.ok true
          else
            beval b2 sigma
  | BExp.isEmpty l =>
      match leval l sigma with
      | Except.error e => Except.error e
      | Except.ok lst => Except.ok lst.isEmpty

def Decl : Type := String -> Bool
def decl_default : Decl := fun _ => false
def updateDecl (D : Decl) (x : String) : Decl :=
  fun y => if y == x then true else D y
def updateBloc (sigma_initial : Env) (sigma_final : Env) (scopeDecl : Decl) : Env :=
  fun x => if scopeDecl x = true then sigma_initial x else sigma_final x
def updateBlocTip (tipenv_initial : TipEnv) (tipenv_final : TipEnv) (scopeDecl : Decl) : TipEnv :=
  fun x => if scopeDecl x = true then tipenv_initial x else tipenv_final x


def FunEnv : Type := String -> Option (List (String × Tip) × Tip × Com)
def funenv_default : FunEnv := fun _ => none
def updateFun (F : FunEnv) (name : String) (parametri : List (String × Tip)) (returnType : Tip) (cod : Com) : FunEnv :=
  fun f => if f == name then some (parametri, returnType, cod) else F f


def Stack : Type := List Value
deriving instance Repr for Stack

def stack_default : Stack := []
def stack_push (v : Value) (S : Stack) : Stack := v :: S
def stack_pop (S : Stack) : (Value × Stack) :=
  match S with
  | [] => (Value.intVal 0, [])
  | v :: S' => (v, S')


partial def eval_args (args : List AExp) (sigma : Env) : Except EvalError (List Int) :=
  match args with
  | [] => Except.ok []
  | a :: as =>
      match aeval a sigma with
      | Except.error e => Except.error e
      | Except.ok v =>
          match eval_args as sigma with
          | Except.error e => Except.error e
          | Except.ok vs => Except.ok (v :: vs)

def update_params : Env → List (String × Tip) → List Int → Env
  | sigma, [], [] => sigma
  | sigma, ((p, _) :: ps), (v :: vs) => update_params (update sigma p (Value.intVal v)) ps vs
  | sigma, _, _ => sigma

def update_params_tip : TipEnv → List (String × Tip) → TipEnv
  | tipenv, [] => tipenv
  | tipenv, ((p, t) :: ps) => update_params_tip (updateTip tipenv p t) ps


def sigma_default : Env := fun _ => NEDECLARAT_VAL

instance : Inhabited Env where
  default := sigma_default

instance : Inhabited Decl where
  default := decl_default

instance : Inhabited TipEnv where
  default := tipenv_default

instance : Inhabited FunEnv where
  default := funenv_default

structure EvalState where
  env : Env
  decl : Decl
  tipenv : TipEnv
  funenv : FunEnv
  stack : Stack


instance : Inhabited EvalState where
  default := {
    env := sigma_default,
    decl := decl_default,
    tipenv := tipenv_default,
    funenv := funenv_default,
    stack := stack_default
  }


def showDeclaredVarsWithTypes (sigma : Env) (decl : Decl) (tipenv : TipEnv) : String :=
  let commonVars := [
    "a", "b", "sum", "diff", "prod", "quot", "rem", "numbers", "mapped",
    "x", "y", "is_less", "is_equal", "is_less_eq", "complex", "disjunct",
    "max", "adevaratt", "conjunctie", "fals",
    "n", "i", "result", "temp",
    "z",
    "numbers", "first", "len", "second", "third",
    "list1", "list2", "combined", "total_len",
    "empty_list", "is_empty", "non_empty", "not_empty",
    "answer", "check1", "check2", "val1", "val2", "input1",
    "is_prime", "divisor", "check_17", "check_15",
    "counter",
    "index", "current",
    "sq1", "sq2",
    "data", "count", "min", "range",
    "exp", "base", "remainder"
  ]
  let bindings := commonVars.filter decl |>.filterMap fun v =>
    match tipenv v with
    | some Tip.Int =>
        match sigma v with
        | Value.intVal i => some s!"{v}: Int = {i}"
        | _ => none
    | some Tip.Bool =>
        match sigma v with
        | Value.intVal i =>
            let boolVal := if i == 1 then "true" else "false"
            some s!"{v}: Bool = {boolVal}"
        | Value.boolVal b =>
            let boolVal := if b then "true" else "false"
            some s!"{v}: Bool = {boolVal}"
        | _ => none
    | some (Tip.List _) =>
        match sigma v with
        | Value.listVal lst => some s!"{v}: List = {repr lst}"
        | _ => none
    | none => none
  if bindings.isEmpty then
    "[]"
  else
    "[" ++ String.intercalate ", " bindings ++ "]"


instance : Repr EvalState where
  reprPrec s _ :=
    let envStr := showDeclaredVarsWithTypes s.env s.decl s.tipenv
    s!"EvalState(env: {envStr}, stack: {repr s.stack})"

partial def eval (fuel : Nat) (c : Com) (s : EvalState) : Except EvalError EvalState :=
  match fuel with
  | 0 => Except.error (EvalError.TypeMismatch "out of fuel")
  | fuel' + 1 =>
      match c with
      | skip => Except.ok s
      | atribuire x e =>
          match s.tipenv x with
          | none => Except.error (EvalError.UndeclaredVariable x)
          | some Tip.Int =>
              match typeCheckAExp e s.tipenv with
              | Except.error err => Except.error err
              | Except.ok Tip.Int =>
                  match aeval e s.env with
                  | Except.error err => Except.error err
                  | Except.ok v => Except.ok { s with env := update s.env x (Value.intVal v) }
              | Except.ok t => Except.error (EvalError.WrongType x Tip.Int t)
          | some t => Except.error (EvalError.WrongType x Tip.Int t)
      | atribuire_bool x b =>
          match s.tipenv x with
          | none => Except.error (EvalError.UndeclaredVariable x)
          | some Tip.Bool =>
              match typeCheckBExp b s.tipenv with
              | Except.error err => Except.error err
              | Except.ok Tip.Bool =>
                  match beval b s.env with
                  | Except.error err => Except.error err
                  | Except.ok v => Except.ok { s with env := update s.env x (Value.boolVal v) }
              | Except.ok t => Except.error (EvalError.WrongType x Tip.Bool t)
          | some t => Except.error (EvalError.WrongType x Tip.Bool t)
      | atribuire_list x l =>
          match s.tipenv x with
          | none => Except.error (EvalError.UndeclaredVariable x)
          | some (Tip.List _) =>
              match typeCheckLExp l s.tipenv with
              | Except.error err => Except.error err
              | Except.ok (Tip.List _) =>
                  match leval l s.env with
                  | Except.error err => Except.error err
                  | Except.ok v => Except.ok { s with env := update s.env x (Value.listVal v) }
              | Except.ok t => Except.error (EvalError.WrongType x (Tip.List Tip.Int) t)
          | some t => Except.error (EvalError.WrongType x (Tip.List Tip.Int) t)
      | declaratie x tip e =>
          if s.decl x then
            Except.error (EvalError.VariableAlreadyDeclared x)
          else
            match typeCheckAExp e s.tipenv with
            | Except.error err => Except.error err
            | Except.ok Tip.Int =>
                if tip != Tip.Int then
                  Except.error (EvalError.TypeMismatch s!"Declaration type mismatch for {x}")
                else
                  match aeval e s.env with
                  | Except.error err => Except.error err
                  | Except.ok v =>
                      Except.ok { s with
                        env := update s.env x (Value.intVal v),
                        decl := updateDecl s.decl x,
                        tipenv := updateTip s.tipenv x tip
                      }
            | Except.ok t => Except.error (EvalError.WrongType x tip t)
      | declaratie_bool x b =>
          if s.decl x then
            Except.error (EvalError.VariableAlreadyDeclared x)
          else
            match typeCheckBExp b s.tipenv with
            | Except.error err => Except.error err
            | Except.ok Tip.Bool =>
                match beval b s.env with
                | Except.error err => Except.error err
                | Except.ok v =>
                    Except.ok { s with
                      env := update s.env x (Value.boolVal v),
                      decl := updateDecl s.decl x,
                      tipenv := updateTip s.tipenv x Tip.Bool
                    }
            | Except.ok t => Except.error (EvalError.WrongType x Tip.Bool t)
      | declaratie_list x tip l =>
          if s.decl x then
            Except.error (EvalError.VariableAlreadyDeclared x)
          else
            match typeCheckLExp l s.tipenv with
            | Except.error err => Except.error err
            | Except.ok (Tip.List elemType) =>
                if tip != Tip.List elemType then
                  Except.error (EvalError.TypeMismatch s!"Declaration type mismatch for {x}")
                else
                  match leval l s.env with
                  | Except.error err => Except.error err
                  | Except.ok v =>
                      Except.ok { s with
                        env := update s.env x (Value.listVal v),
                        decl := updateDecl s.decl x,
                        tipenv := updateTip s.tipenv x (Tip.List elemType)
                      }
            | Except.ok t => Except.error (EvalError.WrongType x (Tip.List Tip.Int) t)
      | secventa c1 c2 =>
          match eval fuel' c1 s with
          | Except.error e => Except.error e
          | Except.ok s' => eval fuel' c2 s'
      | Com.while b body =>
          match typeCheckBExp b s.tipenv with
          | Except.error e => Except.error e
          | Except.ok Tip.Bool =>
              match beval b s.env with
              | Except.error e => Except.error e
              | Except.ok false => Except.ok s
              | Except.ok true =>
                  match eval fuel' body s with
                  | Except.error e => Except.error e
                  | Except.ok s' => eval fuel' (Com.while b body) s'
          | Except.ok t => Except.error (EvalError.TypeMismatch s!"While condition must be Bool, got {repr t}")
      | Com.ite b c1 c2 =>
          match typeCheckBExp b s.tipenv with
          | Except.error e => Except.error e
          | Except.ok Tip.Bool =>
              match beval b s.env with
              | Except.error e => Except.error e
              | Except.ok true => eval fuel' c1 s
              | Except.ok false => eval fuel' c2 s
          | Except.ok t => Except.error (EvalError.TypeMismatch s!"If condition must be Bool, got {repr t}")
      | Com.for init cond pas body =>
          match eval fuel' init s with
          | Except.error e => Except.error e
          | Except.ok s' =>
              eval fuel' (Com.while cond (secventa body pas)) s'
      | bloc body =>
          match eval fuel' body { s with decl := decl_default } with
          | Except.error e => Except.error e
          | Except.ok s' =>
              Except.ok { s with
                env := updateBloc s.env s'.env s'.decl,
                tipenv := updateBlocTip s.tipenv s'.tipenv s'.decl,
                stack := s'.stack
              }
      | declaratie_functie name params returnType body =>
          match s.funenv name with
          | some _ => Except.error (EvalError.FunctionAlreadyDeclared name)
          | none => Except.ok { s with funenv := updateFun s.funenv name params returnType body }
      | apel_functie name args =>
          match s.funenv name with
          | none => Except.error (EvalError.UndeclaredFunction name)
          | some (params, returnType, body) =>
              if returnType != Tip.Int then
                Except.error (EvalError.TypeMismatch s!"Function {name} does not return Int")
              else
                match eval_args args s.env with
                | Except.error e => Except.error e
                | Except.ok vals =>
                    let sigma_args := update_params s.env params vals
                    let tipenv_args := update_params_tip s.tipenv params
                    match eval fuel' body { env := sigma_args, decl := decl_default, tipenv := tipenv_args, funenv := s.funenv, stack := s.stack } with
                    | Except.error e => Except.error e
                    | Except.ok s' => Except.ok { s with stack := s'.stack }
      | apel_functie_bool name args =>
          match s.funenv name with
          | none => Except.error (EvalError.UndeclaredFunction name)
          | some (params, returnType, body) =>
              if returnType != Tip.Bool then
                Except.error (EvalError.TypeMismatch s!"Function {name} does not return Bool")
              else
                match eval_args args s.env with
                | Except.error e => Except.error e
                | Except.ok vals =>
                    let sigma_args := update_params s.env params vals
                    let tipenv_args := update_params_tip s.tipenv params
                    match eval fuel' body { env := sigma_args, decl := decl_default, tipenv := tipenv_args, funenv := s.funenv, stack := s.stack } with
                    | Except.error e => Except.error e
                    | Except.ok s' => Except.ok { s with stack := s'.stack }
      | Com.return x =>
          match s.tipenv x with
          | none => Except.error (EvalError.UndeclaredVariable x)
          | some _ => Except.ok { s with stack := stack_push (s.env x) s.stack }
      | pop x =>
        if !s.decl x then
          Except.error (EvalError.UndeclaredVariable x)
        else
          match s.tipenv x with
          | none => Except.error (EvalError.UndeclaredVariable x)
          | some varType =>
              let (v, s') := stack_pop s.stack
              match v, varType with
              | Value.intVal _, Tip.Int => Except.ok { s with env := update s.env x v, stack := s' }
              | Value.boolVal _, Tip.Bool => Except.ok { s with env := update s.env x v, stack := s' }
              | Value.intVal _, Tip.Bool => Except.ok { s with env := update s.env x v, stack := s' }
              | Value.listVal _, Tip.List _ => Except.ok { s with env := update s.env x v, stack := s' }
              | _, _ => Except.error (EvalError.TypeMismatch "Stack value type mismatch")

def initial_state : EvalState :=
  { env := sigma_default, decl := decl_default, tipenv := tipenv_default, funenv := funenv_default, stack := stack_default }

def err_division_by_zero : Com :=
  "x" :::= Tip.Int, 10 ;;
  "y" :::= Tip.Int, 0 ;;
  "result" :::= Tip.Int, "x" /' "y"
#eval eval 1000 err_division_by_zero initial_state


def err_modulo_by_zero : Com :=
  "x" :::= Tip.Int, 15 ;;
  "result" :::= Tip.Int, "x" %' 0
#eval eval 1000 err_modulo_by_zero initial_state

def err_type_mismatch_bool_as_int : Com :=
  "flag" :::=b BExp.T ;;
  "x" :::= Tip.Int, 5 ;;
  "result" :::= Tip.Int, "flag" +' "x"
#eval eval 1000 err_type_mismatch_bool_as_int initial_state

def err_type_mismatch_list_as_int : Com :=
  "numbers" :::=l (Tip.List Tip.Int), LExp.cons 1 (LExp.cons 2 (LExp.empty Tip.Int)) ;;
  "result" :::= Tip.Int, "numbers" +' 5
#eval eval 1000 err_type_mismatch_list_as_int initial_state

def err_undeclared_variable : Com :=
  "x" :::= Tip.Int, 10 ;;
  "y" ::= "z" +' "x"
#eval eval 1000 err_undeclared_variable initial_state

def err_variable_already_declared : Com :=
  "x" :::= Tip.Int, 10 ;;
  "x" :::= Tip.Int, 20
#eval eval 1000 err_variable_already_declared initial_state

def err_redeclare_different_type : Com :=
  "flag" :::=b BExp.T ;;
  "flag" :::= Tip.Int, 5
#eval eval 1000 err_redeclare_different_type initial_state

def err_function_already_declared : Com :=
  declaratie_functie "calculeaza" [("x", Tip.Int)] Tip.Int (
    "result" :::= Tip.Int, "x" *' 2 ;;
    Com.return "result"
  ) ;;
  declaratie_functie "calculeaza" [("y", Tip.Int)] Tip.Int (
    "result" :::= Tip.Int, "y" +' 5 ;;
    Com.return "result"
  )
#eval eval 1000 err_function_already_declared initial_state

def err_undeclared_function : Com :=
  "x" :::= Tip.Int, 0 ;;
  apel_functie "chestie" [5, 10] ;;
  pop "x"
#eval eval 1000 err_undeclared_function initial_state

def err_wrong_type_declaration : Com :=
  "x" :::= Tip.Bool, 42
#eval eval 1000 err_wrong_type_declaration initial_state

def err_return : Com :=
  declaratie_functie "getBool" [("x", Tip.Int)] Tip.Bool (
    "result" :::=b ("x" <' 10) ;;
    Com.return "result"
  ) ;;
  "value" :::= Tip.Int, 0 ;;
  apel_functie "getBool" [5] ;;
  pop "value"
#eval eval 1000 err_return initial_state

def err_empty_list_head : Com :=
  "empty" :::=l (Tip.List Tip.Int), LExp.empty Tip.Int ;;
  "first" :::= Tip.Int, AExp.head (LExp.var "empty")
#eval eval 1000 err_empty_list_head initial_state

def err_index_negative : Com :=
  "numbers" :::=l (Tip.List Tip.Int), LExp.cons 1 (LExp.cons 2 (LExp.cons 3 (LExp.empty Tip.Int))) ;;
  "value" :::= Tip.Int, AExp.nth (LExp.var "numbers") (0 -' 5)
#eval eval 1000 err_index_negative initial_state

def err_empty : Com :=
  "x" :::= Tip.Int, 42 ;;
  "check" :::=b BExp.isEmpty (LExp.var "x")

#eval eval 1000 err_empty initial_state


def ex_aexp : Com :=
  "a" :::= Tip.Int, 15 ;;
  "b" :::= Tip.Int, 4 ;;
  "sum" :::= Tip.Int, "a" +' "b" ;;
  "diff" :::= Tip.Int, "a" -' "b" ;;
  "prod" :::= Tip.Int, "a" *' "b" ;;
  "quot" :::= Tip.Int, "a" /' "b" ;;
  "rem" :::= Tip.Int, "a" %' "b"

#eval eval 1000 ex_aexp initial_state


def ex_bexp : Com :=
  "x" :::= Tip.Int, 10 ;;
  "y" :::= Tip.Int, 20 ;;
  "is_less" :::=b ("x" <' "y") ;;
  "is_equal" :::=b ("x" ==' "y") ;;
  "is_less_eq" :::=b ("x" <=' "y") ;;
  "complex" :::=b (("x" <' "y") and' (!' ("x" ==' "y"))) ;;
  "disjunct" :::=b (("x" <' 5) or' ("y" <' 25))

#eval eval 1000 ex_bexp initial_state

def ex_if : Com :=
  "a" :::= Tip.Int, 42 ;;
  "b" :::= Tip.Int, 37 ;;
  "max" :::= Tip.Int, 0 ;;
  ite ("a" <' "b")
    ("max" ::= "b")
    ("max" ::= "a")

#eval eval 1000 ex_if initial_state


def ex_if_in_if : Com :=
  "a" :::= Tip.Int, 15 ;;
  "b" :::= Tip.Int, 20 ;;
  "diff" :::= Tip.Int, 0 ;;
  ite ("a" <' "b")
    ("diff" ::= "b" -' "a")
    (ite ("a" ==' "b")
      ("diff" ::= 0)
      ("diff" ::= "a" -' "b"))

#eval eval 1000 ex_if_in_if initial_state

def ex_while_suma_gauss : Com :=
  "n" :::= Tip.Int, 10 ;;
  "sum" :::= Tip.Int, 0 ;;
  "i" :::= Tip.Int, 1 ;;
  Com.while ("i" <=' "n")
    ("sum" ::= "sum" +' "i" ;;
     "i" ::= "i" +' 1)

#eval eval 1000 ex_while_suma_gauss initial_state


def ex_for_factorial : Com :=
  "n" :::= Tip.Int, 6 ;;
  "result" :::= Tip.Int, 1 ;;
  Com.for
    ("i" :::= Tip.Int, 1)
    ("i" <=' "n")
    ("i" ::= "i" +' 1)
    ("result" ::= "result" *' "i")

#eval eval 1000 ex_for_factorial initial_state


def ex_block_scope : Com :=
  "x" :::= Tip.Int, 10 ;;
  "y" :::= Tip.Int, 20 ;;
  {
    "x" :::= Tip.Int, 5 ;;
    "z" :::= Tip.Int, 15 ;;
    "y" ::= "x" +' "z"
  } ;;
  "result" :::= Tip.Int, "x" +' "y"

#eval eval 1000 ex_block_scope initial_state

def ex_liste : Com :=
  "numbers" :::=l (Tip.List Tip.Int),
    LExp.cons 5 (LExp.cons 10 (LExp.cons 15 (LExp.cons 20 (LExp.empty Tip.Int)))) ;;
  "first" :::= Tip.Int, AExp.head (LExp.var "numbers") ;;
  "len" :::= Tip.Int, AExp.length (LExp.var "numbers") ;;
  "second" :::= Tip.Int, AExp.nth (LExp.var "numbers") 1 ;;
  "third" :::= Tip.Int, AExp.nth (LExp.var "numbers") 2

#eval eval 1000 ex_liste initial_state


def ex_concatenare : Com :=
  "list1" :::=l (Tip.List Tip.Int), LExp.cons 1 (LExp.cons 2 (LExp.empty Tip.Int)) ;;
  "list2" :::=l (Tip.List Tip.Int), LExp.cons 3 (LExp.cons 4 (LExp.empty Tip.Int)) ;;
  "combined" :::=l (Tip.List Tip.Int), LExp.append (LExp.var "list1") (LExp.var "list2") ;;
  "total_len" :::= Tip.Int, AExp.length (LExp.var "combined")

#eval eval 1000 ex_concatenare initial_state


def ex_list_check : Com :=
  "empty_list" :::=l (Tip.List Tip.Int), LExp.empty Tip.Int ;;
  "is_empty" :::=b isEmpty (LExp.var "empty_list") ;;
  "non_empty" :::=l (Tip.List Tip.Int), LExp.cons 1 (LExp.empty Tip.Int) ;;
  "not_empty" :::=b isEmpty (LExp.var "non_empty")

#eval eval 1000 ex_list_check initial_state

def ex_functie : Com :=
  declaratie_functie "multiply" [("x", Tip.Int), ("y", Tip.Int)] Tip.Int (
    "result" :::= Tip.Int, "x" *' "y" ;;
    Com.return "result"
  ) ;;
  "answer" :::= Tip.Int, 0 ;;
  apel_functie "multiply" [7, 6] ;;
  pop "answer"

#eval eval 1000 ex_functie initial_state


def ex_functie_bool : Com :=
  declaratie_functie "isEven" [("n", Tip.Int)] Tip.Bool (
    "remainder" :::= Tip.Int, "n" %' 2 ;;
    "result" :::=b ("remainder" ==' 0) ;;
    Com.return "result"
  ) ;;
  "check1" :::=b BExp.F ;;
  "check2" :::=b BExp.F ;;
  apel_functie_bool "isEven" [10] ;;
  pop "check1" ;;
  apel_functie_bool "isEven" [7] ;;
  pop "check2"

#eval eval 1000 ex_functie_bool initial_state

def ex_func_abs : Com :=
  declaratie_functie "abs" [("n", Tip.Int)] Tip.Int (
    ite ("n" <' 0)
      ("result" :::= Tip.Int, 0 -' "n" ;; Com.return "result")
      ("result" :::= Tip.Int, "n" ;; Com.return "result")
  ) ;;
  "val1" :::= Tip.Int, 0 ;;
  "val2" :::= Tip.Int, 0 ;;
  "input1" :::= Tip.Int, 15 ;;
  "input1" ::= 0 -' "input1" ;;
  apel_functie "abs" ["input1"] ;;
  pop "val1" ;;
  apel_functie "abs" [20] ;;
  pop "val2"

#eval eval 1000 ex_func_abs initial_state


def ex_func_putere : Com :=
  declaratie_functie "power" [("base", Tip.Int), ("exp", Tip.Int)] Tip.Int (
    "result" :::= Tip.Int, 1 ;;
    "counter" :::= Tip.Int, 0 ;;
    Com.while ("counter" <' "exp")
      ("result" ::= "result" *' "base" ;;
       "counter" ::= "counter" +' 1) ;;
    Com.return "result"
  ) ;;
  "answer" :::= Tip.Int, 0 ;;
  apel_functie "power" [2, 8] ;;
  pop "answer"

#eval eval 1000 ex_func_putere initial_state

def ex_prim : Com :=
  declaratie_functie "isPrime" [("n", Tip.Int)] Tip.Bool (
    "is_prime" :::=b BExp.T ;;
    ite ("n" <=' 1)
      ("is_prime" ::=b BExp.F)
      (
        "divisor" :::= Tip.Int, 2 ;;
        Com.while (("divisor" *' "divisor") <=' "n")
          (ite (("n" %' "divisor") ==' 0)
            ("is_prime" ::=b BExp.F ;;
             "divisor" ::= "n" +' 1)
            ("divisor" ::= "divisor" +' 1))
      ) ;;
    Com.return "is_prime"
  ) ;;
  "check_17" :::=b BExp.F ;;
  "check_17" ::=b BExp.F ;;
  "check_15" :::=b BExp.F ;;
  apel_functie_bool "isPrime" [17] ;;
  pop "check_17" ;;
  apel_functie_bool "isPrime" [15] ;;
  pop "check_15"

#eval eval 1000 ex_prim initial_state


def ex_fibonacci : Com :=
  "n" :::= Tip.Int, 10 ;;
  "a" :::= Tip.Int, 0 ;;
  "b" :::= Tip.Int, 1 ;;
  "sum" :::= Tip.Int, 0 ;;
  "counter" :::= Tip.Int, 0 ;;
  Com.while ("counter" <' "n")
    ("sum" ::= "sum" +' "a" ;;
     "temp" :::= Tip.Int, "a" +' "b" ;;
     "a" ::= "b" ;;
     "b" ::= "temp" ;;
     "counter" ::= "counter" +' 1)

#eval eval 1000 ex_fibonacci initial_state


def ex_list_sum : Com :=
  "numbers" :::=l (Tip.List Tip.Int),
    LExp.cons 10 (LExp.cons 20 (LExp.cons 30 (LExp.cons 40 (LExp.empty Tip.Int)))) ;;
  "sum" :::= Tip.Int, 0 ;;
  "index" :::= Tip.Int, 0 ;;
  "len" :::= Tip.Int, AExp.length (LExp.var "numbers") ;;
  Com.while ("index" <' "len")
    {"current" :::= Tip.Int, AExp.nth (LExp.var "numbers") "index" ;;
     "sum" ::= "sum" +' "current" ;;
     "index" ::= "index" +' 1}

#eval eval 1000 ex_list_sum initial_state

def ex_functie_in_functie : Com :=
  declaratie_functie "square" [("x", Tip.Int)] Tip.Int (
    "result" :::= Tip.Int, "x" *' "x" ;;
    Com.return "result"
  ) ;;
  declaratie_functie "sumOfSquares" [("a", Tip.Int), ("b", Tip.Int)] Tip.Int (
    "sq1" :::= Tip.Int, 0 ;;
    "sq2" :::= Tip.Int, 0 ;;
    apel_functie "square" ["a"] ;;
    pop "sq1" ;;
    apel_functie "square" ["b"] ;;
    pop "sq2" ;;
    "result" :::= Tip.Int, "sq1" +' "sq2" ;;
    Com.return "result"
  ) ;;
  "answer" :::= Tip.Int, 0 ;;
  apel_functie "sumOfSquares" [3, 4] ;;
  pop "answer"

#eval eval 1000 ex_functie_in_functie initial_state


def ex_procesare_lista : Com :=
  "data" :::=l (Tip.List Tip.Int),
    LExp.cons 15 (LExp.cons 8 (LExp.cons 23 (LExp.cons 12 (LExp.cons 19 (LExp.empty Tip.Int))))) ;;
  "count" :::= Tip.Int, AExp.length (LExp.var "data") ;;
  "sum" :::= Tip.Int, 0 ;;
  "min" :::= Tip.Int, AExp.head (LExp.var "data") ;;
  "max" :::= Tip.Int, AExp.head (LExp.var "data") ;;
  "i" :::= Tip.Int, 0 ;;
  Com.while ("i" <' "count")
    {"current" :::= Tip.Int, AExp.nth (LExp.var "data") "i" ;;
     "sum" ::= "sum" +' "current" ;;
     ite ("current" <' "min")
       ("min" ::= "current")
       skip ;;
     ite ("max" <' "current")
       ("max" ::= "current")
       skip ;;
     "i" ::= "i" +' 1} ;;
  "range" :::= Tip.Int, "max" -' "min"

#eval eval 1000 ex_procesare_lista initial_state

def ex_idk_fr : Com :=
  "adevaratt" :::=b BExp.T ;;
  "fals" :::=b BExp.F ;;
  "conjunctie" :::=b "adevaratt" or' "fals"

#eval eval 1000 ex_idk_fr initial_state

def ex_factorial_recursive : Com :=
  declaratie_functie "factorial" [("n", Tip.Int)] Tip.Int (
    ite ("n" <=' 1)
      ("result" :::= Tip.Int, 1 ;;
       Com.return "result")
      ("n_minus_1" :::= Tip.Int, "n" -' 1 ;;
       "rec_result" :::= Tip.Int, 0 ;;
       apel_functie "factorial" ["n_minus_1"] ;;
       pop "rec_result" ;;
       "result" :::= Tip.Int, "n" *' "rec_result" ;;
       Com.return "result")
  ) ;;
  "answer" :::= Tip.Int, 0 ;;
  apel_functie "factorial" [5] ;;
  pop "answer"

#eval eval 1000 ex_factorial_recursive initial_state
