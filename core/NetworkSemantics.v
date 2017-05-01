Require Import List.
Import ListNotations.
Require Import Bool.

Require Import StructTact.StructTactics.
Require Import StructTact.RemoveAll.
Require Import StructTact.Update.

Set Implicit Arguments.

Section Verdi.

(* We first define the elements our the World in our Network {Base Types} *)
Variable Node : Type.
Variable State : Type.
Variable Msg : Type.
Variable Input : Type.
Variable Output : Type.

(* We now define an : ExternalEvent, Packet {Sum, Product Types} *)
Definition ExternalEvent : Type := Node * (Input + Output).

(* A Packet *)
Record Packet : Type :=
  {
    dest : Node;
    payload : Msg
  }.

Variable Node_eq_dec : forall x y : Node, {x = y} + {x <> y}.
Variable Packet_eq_dec : forall x y : Packet, {x = y} + {x <> y}.

(* We finally define the 3-Tuple of the World as a Record : localState, inFlightPackets, trace } *)
Record World : Type :=
  {
    localState : Node -> State;
    inFlightPackets : list Packet;
    trace : list ExternalEvent
  }.

(* For all of our Semantics, we need a Set of Event-Handlers. These tell us how to 'evolve' the World when I/O Events occur *)
Variable InitState : Node -> State. (* Configures our Distributed System to an Initial State *)

Variable ProcessMsg : Node -> Msg -> State -> (State * list Packet * list Output). (* Configures how our Distributed System evolves when a 2-tuple (Node, Msg) is passed to the System *)

Variable ProcessInput : Node -> Input -> State -> (State * list Packet * list Output). (* Configures how our Distributed System evolves when a 2-tuple (Node, Input) is passed to the System *)

(* The Semantics *)
(* Initialize a World *)
Definition InitWorld : World := Build_World InitState [] [].

(* The record_outputs function *)
Fixpoint record_outputs (n: Node) (outs: list Output) : list ExternalEvent :=
  match outs with
    | [] => []
    | x :: xs => ((n, inr x)) :: (record_outputs n xs)
  end.

(* A Reliable Step, provides support for : i) Evolving on receinv a Message ii) Evolving on receiving an Input *)
Inductive reliable_step : World -> World -> Prop :=
| step_input :
    forall w i n st' ps outs,
      ProcessInput n i (localState w n) = (st', ps, outs) ->
      reliable_step w
        (Build_World
           (update Node_eq_dec (localState w) n st')
           (ps ++ inFlightPackets w)
           (trace w ++ [(n, inl i)] ++ record_outputs n outs))
| step_msg :
    forall w p st' ps outs,
      In p (inFlightPackets w) ->
      ProcessMsg (dest p) (payload p) (localState w (dest p)) = (st', ps, outs) ->
      reliable_step w
      (Build_World
         (update Node_eq_dec (localState w) (dest p) st')
         (ps ++ (remove_all Packet_eq_dec [p] (inFlightPackets w)))
         (trace w ++ record_outputs (dest p) outs)).

End Verdi.
