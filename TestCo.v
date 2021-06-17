From Coq Require Export String.
(* Require to fix errors like `No interpretation for string "1"` *)
Open Scope string_scope.
From Coq Require Export Nat.
From Coq Require Export List.
Import ListNotations.

Require Extraction.
(* export string as char list. Not idea how to do it properly *)
From Coq  Require ExtrOcamlString.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Check (Some 1).

Section listAssoc.
  Variable A: Type.
  Fixpoint find  (xs: list (string * A)) (k: string) : option A :=
    match xs with
    | [] => None
    | (h,v) :: tl => if String.eqb h k then Some v else find tl k
    end.
End listAssoc.
Search "find".

Check eq_refl : None = find string [] "1".
Check eq_refl : (Some O) = find nat [ ("1", O) ] "1".



Section unif.
  Inductive term :=
  | Var : string -> term
  | EInt : nat -> term
  | ENil : term
  | ECons : term -> term -> term.

  Inductive subst := Subst : list (string * term) -> subst.

  Definition empty_subst := (Subst []).

  Fixpoint walk (v: term) (s: subst): term :=
    match v with
    | EInt _ => v
    | ENil => v
    | ECons l r => ECons (walk l s) (walk r s)
    | Var s => Var s
    end.

  Definition extend s k v :=
    match s with
    | Subst ss => Subst ( (k,v) :: ss)
    end.

  Definition unify_helper x y (acc: option subst) :=
    match acc with
    | None => None
    | Some s =>
      match walk x s, walk y s with
      | (Var sx), (Var sy) =>
          if String.eqb sx sy
          then acc
          else Some (extend s sx (Var sy))
      | r, (Var sx) => Some (extend s sx r)
      | (Var sx), r => Some (extend s sx r)
      | EInt l, EInt r =>
          if Nat.eqb l r then acc else None
      | EInt _, ECons _ _
      | ECons _ _, EInt _
      | ENil, _ | _, ENil
      | ECons _ _, _  => None
      end
    end.

  Definition unify x y := unify_helper x y None.

End unif.
(* Extraction "TestCo.ml" term. *)


Section stream2.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream
  | Delay : stream -> stream
  | Nil : stream
  .
(*
  Inductive WellFoundStream (s: stream) : Prop :=
  | WFSNil  : (s=Nil) ->  WellFoundStream s
  | WFSCons : forall (a:A) (tl: stream),
      (s = Cons a tl) -> WellFoundStream tl -> WellFoundStream s
  | WFSDelay: forall (tl: stream),
      (s = Delay tl) -> WellFoundStream tl -> WellFoundStream s.
*)
  (* https://www.labri.fr/perso/casteran/RecTutorial.pdf *)
  Print Acc.

  Definition force l :=
    match l with
    | Delay s => s
    | s => s
    end.

  Fail CoFixpoint mplus (l r: stream)  : stream :=
    match l with
    | Nil => r
    | Cons h tl => Cons h (mplus r tl)
    | Delay old => mplus r old
    end.

  Fail CoFixpoint mplus (l r: stream) : stream :=
    match l with
    | Nil => r
    | Cons h tl => Cons h (mplus r tl)
    | Delay old =>
        match r with
        | Nil => old
        | Cons h tl => Cons h (mplus old tl)
        | Delay old2 => mplus old old2
        end
    end.

  Fail CoFixpoint mplus (xs ys: stream) :=
    match xs with
    | Nil => force ys
    | Cons h tl => Cons h (mplus r tl)
    | Delay _ => Delay (mplus (force r) old)
    end.

End stream2.



Module Stream3.

  (* TODO: remeber that streams is extracted with Lazy *)
  CoInductive stream (A: Type): Type :=
  | Cons : A -> stream A -> stream A
  | Delay : stream A -> stream A
  | Nil : stream A.

  Definition from_fun z := Delay z.

  (* Added only to `force` the stream that will be extracted
    as OCaml lazy value *)
  Definition force_lazy {A: Type} (s: stream A) :=
    match s with
    | Nil _ => Nil _
    | Delay _ s => Delay _ s
    | Cons _ h tl => Cons _ h tl
    end.

  (* Removes Delay constructor *)
  Definition force {A: Type} (x: stream A) :=
    match x with
    | Delay _ zz => force_lazy zz
    | xs => xs end.

  CoFixpoint mplus {A: Type} (xs ys: stream A) :=
    match xs with
    | Nil _ => force ys
    | Cons _ x xs => Cons _ x (from_fun A (mplus (force ys) xs))
    | Delay _ _ => from_fun _ (mplus (force ys) xs)
    end.

  CoFixpoint bind {A: Type} (s: stream A) (f: A -> stream A) : stream A :=
    match s with
    | Nil _ => Nil _
    | Cons _ x tl =>
        (* TODO: prove that mplus either introduces constructor
                                  or doesn't do recursive call
                                  *)
        mplus (force_lazy (f x))
          (from_fun _ (bind (force tl) f))
    | Delay _ zz => from_fun _ (bind (force_lazy zz) f)
    end.

  (*
  Recursive definition of bind is ill-formed.
  In environment
  bind :
  forall (A : Type) (_ : stream A) (_ : forall _ : A, stream A), stream A
  A : Type
  s : stream A
  f : forall _ : A, stream A
  x : A
  tl : stream A
  Unguarded recursive call in
  "cofix mplus (A : Type) (xs ys : stream A) : stream A :=
    match xs with
    | Cons _ x xs0 => Cons A x (from_fun A (mplus A (force ys) xs0))
    | Delay _ _ => from_fun A (mplus A (force ys) xs)
    | Nil _ => force ys
    end".
  Recursive definition is:
  "fun (A : Type) (s : stream A) (f : forall _ : A, stream A) =>
  match s with
  | Cons _ x tl => mplus (f x) (from_fun A (bind A (force tl) f))
  | Delay _ zz => from_fun A (bind A (force_lazy zz) f)
  | Nil _ => Nil A
  end".
  *)

End Stream3.

Section MK.




End MK.


(* Extraction "TestCo.ml" stream term unify. *)
