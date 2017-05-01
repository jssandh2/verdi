Require Import Verdi.NetworkSemantics.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

(* NOTE : We first define the {Nat} Type, and {State := Nat}. *)
(* We will add the {plus,minus} operators to provide for the {inc,dec} operations *)
Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

(* Definition of the {plus,minus} functions *)
Fixpoint plus (n: Nat) (m: Nat) : Nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
end.

Fixpoint minus (n m: Nat) : Nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
end.

(* The 2 Nodes *)
Inductive Node := primary | backup.

(* The Vaid Messages *)
Inductive Msg : Type :=
  | inc' : Nat -> Msg
  | inc : Msg
  | dec : Nat -> Msg
  | ack_inc : Msg
  | ack_dec : Msg.

(* The valid Inputs *)
Inductive Input : Type :=
  | request_inc : Input
  | request_inc' : Nat -> Input
  | request_dec : Nat -> Input.

(* The valid Outputs *)
Inductive Output := inc_executed | dec_executed.

(* The state of the System *)
Definition State := Nat.

(* OVERRIDEN : We now define an : ExternalEvent, Packet {Sum, Product Types} *)
Definition ExternalEvent : Type := Node * (Input + Output).

(* OVERRIDEN : A Packet *)
Record Packet : Type :=
  {
    dest : Node;
    payload : Msg
  }.

(* Initial State configuration for : primary, backup *)
Definition InitState (_: Node) := 0.

(* Handler Monads *)
Definition handler_monad (A: Type): Type :=
  State -> A * State * list Packet * list Output.

Definition handler :=
  State -> State * list Packet * list Output.

(* Let us now define the {bind, ret} monadic operators *)
Definition ret {A: Type} (a: A) : handler_monad A := fun s => (a, s, [], []).

Definition bind {A B: Type} (m: handler_monad A) (f: A -> handler_monad B): handler_monad B :=
  fun s =>
    let '(a, s', ps1, outs1) := m s in
    let '(b, s'', ps2, outs2) := f a s' in
    (b, s'', ps1 ++ ps2, outs1 ++ outs2).

(* Monadic {get,set,send,out,nop} methods with implicit argument provision for {get} *)
Definition set (s: State) : handler_monad unit := fun _ => (tt, s, [], []).

Definition get : handler_monad State := fun s => (s, s, [], []).

Definition send (p: Packet) : handler_monad unit := fun s => (tt, s, [p], []).

Definition out (o: Output) : handler_monad unit := fun s => (tt, s, [], [o]).

Definition nop := @ret _ tt.

(* Some Notation for the Monadic operations, allowing for 'Pipelining' *)
Notation "x <- c1 ;; c2" := (@bind _ _ c1 (fun x => c2))
                              (at level 100, c1 at next level, right associativity).

Notation "e1 ;; e2" := (_ <- e1 ;; e2)
                         (at level 100, right associativity).

(* Increment and Decrement Operations *)
Definition do_inc : handler_monad unit :=
  x <- get ;; set (plus x (S O)).

Definition do_inc' (n: Nat) : handler_monad unit :=
  x <- get ;; set (plus x n).

Definition do_dec (n: Nat) : handler_monad unit :=
  x <- get ;; set (minus x n).

(* Functions to Process : {Input, Msg} *)
Definition processInput (n: Node) (i: Input) : handler_monad unit :=
  match n with
    | primary => match i with
                   | request_inc => do_inc;; send (Build_Packet (backup) (inc))
                   | request_inc' n => do_inc' n;; (send (Build_Packet (backup) (inc' n)))
                   | request_dec n => do_dec n;; (send (Build_Packet (backup) (dec n)))
                 end
    | backup => nop
  end.

Definition processMsg (n: Node) (m: Msg) : handler_monad unit :=
  match n with
    | primary => match m with
                   | ack_inc => out inc_executed
                   | ack_dec => out dec_executed
                   | _ => nop
                 end
    | backup => match m with
                  | inc => do_inc;; send (Build_Packet (primary) (ack_inc))
                  | inc' n => do_inc' n;; (send (Build_Packet (primary) (ack_inc)))
                  | dec n => do_dec n;; (send (Build_Packet (primary) (ack_dec)))
                  | _ => nop
                end
  end.

(* TODO :: i) Addition of Reliable_Semantics for Duplication. ii) Inductive Proofs for the System *)
