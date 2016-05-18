Require Import DynamicNet.
Require Import Chord.
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import StructTact.StructTactics.

Section ChordProof.
  Variable SUCC_LIST_LEN : nat.
  Variable hash : addr -> id.
  Variable hash_inj : forall a b : addr,
      hash a = hash b -> a = b.
  Variable base : list addr.
  Variable base_size : length base = SUCC_LIST_LEN + 1.

  Notation start_handler := (start_handler SUCC_LIST_LEN hash).
  Notation recv_handler := (recv_handler SUCC_LIST_LEN hash).
  Notation timeout_handler := (timeout_handler hash).
  Notation tick_handler := (tick_handler hash).

  Notation handle_query := (handle_query SUCC_LIST_LEN hash).
  Notation handle_query_timeout := (handle_query_timeout hash).
  Notation send := (send addr payload).

  Notation global_state := (global_state addr payload data timeout).
  Notation nodes := (nodes addr payload data timeout).
  Notation failed_nodes := (failed_nodes addr payload data timeout).
  Notation sigma := (sigma addr payload data timeout).
  Notation update := (update addr addr_eq_dec data).

  Notation apply_handler_result := (apply_handler_result addr addr_eq_dec payload data timeout timeout_eq_dec).
  Notation end_query := (end_query hash).
  Notation start_query := (start_query hash).
  Notation handle_stabilize := (handle_stabilize SUCC_LIST_LEN hash).
  Notation try_rectify := (try_rectify hash).

  Notation step_dynamic := (step_dynamic addr addr_eq_dec payload data timeout timeout_eq_dec start_handler recv_handler timeout_handler client_payload can_be_client can_be_node).

  Notation e_recv := (e_recv addr payload timeout).
  Notation e_timeout := (e_timeout addr payload timeout).
  Notation e_fail := (e_fail addr payload timeout).

  Axiom timeouts_detect_failure : forall trace xs ys t h dead req,
      trace = xs ++ t :: ys ->
      (* if a request timeout occurs at some point in the trace... *)
      t = (e_timeout h (Request dead req)) ->
      (* then it corresponds to an earlier node failure. *)
      In (e_fail dead) xs.

  (* tip: treat this as opaque and use lemmas: it never gets stopped except by failure *)
  Definition live_node (gst : global_state) (h : addr) : Prop :=
    exists st,
      sigma gst h = Some st /\
      joined st = true /\
      In h (nodes gst) /\
      ~ In h (failed_nodes gst).

  Definition dead_node (gst : global_state) (h : addr) : Prop :=
    exists st,
      sigma gst h = Some st /\
      In h (nodes gst) /\
      In h (failed_nodes gst).

  Definition joining_node (gst : global_state) (h : addr) : Prop :=
    exists st,
      sigma gst h = Some st /\
      joined st = false /\
      In h (nodes gst) /\
      ~ In h (failed_nodes gst).

  Theorem live_node_characterization : forall gst h st,
      sigma gst h = Some st ->
      joined st = true ->
      In h (nodes gst) ->
      ~ In h (failed_nodes gst) ->
      live_node gst h.
  Proof.
    unfold live_node.
    intuition.
    match goal with
      | x : data |- exists _ : data, _ => exists x
    end.
    intuition.
  Qed.

  Definition live_node_dec (gst : global_state) (h : addr) :=
    match sigma gst h with
      | Some st => if joined st
                   then if in_dec addr_eq_dec h (nodes gst)
                        then if in_dec addr_eq_dec h (failed_nodes gst)
                             then false
                             else true
                        else false
                   else false
      | None => false
    end.

  Ltac break_step :=
    match goal with
      | H : step_dynamic _ _ |- _ =>
        induction H
    end.

  Ltac break_live_node :=
    match goal with
      | H : live_node _ _ |- _ =>
        unfold live_node in H; break_exists; repeat break_and
    end.

  Ltac break_live_node_exists_exists :=
    match goal with
      | H : live_node _ _ |- _ =>
        unfold live_node in H; break_exists_exists; repeat break_and
    end.

  Ltac break_dead_node :=
    match goal with
      | H : dead_node _ _ |- _ =>
        unfold dead_node in H; break_exists; repeat break_and
    end.

  Theorem live_node_dec_equiv_live_node : forall gst h,
      live_node gst h <-> live_node_dec gst h = true.
  Proof.
    unfold live_node_dec.
    intuition.
    - repeat break_match;
        break_live_node;
        congruence || auto.
    - repeat break_match;
        congruence || eauto using live_node_characterization.
  Qed.

  Definition best_succ (gst : global_state) (h s : addr) : Prop :=
    exists st xs ys,
      live_node gst h /\
      sigma gst h = Some st /\
      map addr_of (succ_list st) = xs ++ s :: ys /\
      (forall o, In o xs -> dead_node gst o) /\
      live_node gst s.

  (* transitive closure of best_succ *)
  (* treat as opaque *)
  Inductive reachable (gst : global_state) : addr -> addr -> Prop :=
    | ReachableSucc : forall from to,
        best_succ gst from to ->
        reachable gst from to
    | ReachableTransL : forall from x to,
        best_succ gst from x ->
        reachable gst x to ->
        reachable gst from to.

  Ltac induct_reachable :=
    match goal with
      | H : reachable _ _ _ |- _ =>
        induction H
    end.

  Lemma ReachableTransR : forall gst from x to,
      reachable gst from x ->
      best_succ gst x to ->
      reachable gst from to.
  Proof.
    intuition.
    induct_reachable.
    - eapply ReachableTransL.
      eauto.
      eapply ReachableSucc.
      eauto.
    - eauto using ReachableTransL.
  Qed.

  Lemma ReachableTrans : forall gst from x to,
      reachable gst from x ->
      reachable gst x to ->
      reachable gst from to.
  Proof.
    intros gst from x to H.
    generalize dependent to.
    induction H.
    - intuition.
      eauto using ReachableSucc, ReachableTransL.
    - intuition.
      eauto using ReachableSucc, ReachableTransL.
  Qed.

  Definition best_succ_of (gst : global_state) (h : addr) : option addr :=
    match (sigma gst) h with
      | Some st => head (filter (live_node_dec gst) (map addr_of (succ_list st)))
      | None => None
    end.

  (* treat as opaque *)
  Definition ring_member (gst : global_state) (h : addr) : Prop :=
    reachable gst h h.

  Definition at_least_one_ring (gst : global_state) : Prop :=
    exists h, ring_member gst h.

  Definition at_most_one_ring (gst : global_state) : Prop :=
    forall x y,
      ring_member gst x ->
      ring_member gst y ->
      reachable gst x y.

  Definition between (x y z : id) :=
    x < y < z \/ y < z < x \/ z < x < y.

  Definition ordered_ring (gst : global_state) : Prop :=
    forall h s x,
      ring_member gst h ->
      best_succ gst h s ->
      ring_member gst x ->
      ~ between h x s. (* TODO fix between semantics *)
      (* or between h x s -> s = x *)

  Definition connected_appendages (gst : global_state) : Prop :=
    forall a, exists r,
      live_node gst a ->
      ring_member gst r /\ reachable gst a r.

  Definition base_not_skipped (gst : global_state) : Prop :=
    forall h b succs xs s ys st,
      live_node gst h ->
      Some st = sigma gst h ->
      succs = map addr_of (succ_list st) ->
      xs ++ s :: ys = succs ->
      In b base ->
      between h b s ->
      In b xs.

  Definition inductive_invariant (gst : global_state) : Prop :=
    at_least_one_ring gst /\
    at_most_one_ring gst /\
    ordered_ring gst /\
    connected_appendages gst /\
    base_not_skipped gst.

  Ltac break_invariant :=
    match goal with
      | H : inductive_invariant _ |- _ =>
        unfold inductive_invariant in H; break_and
    end.

  Lemma live_node_specificity : forall gst gst',
      nodes gst = nodes gst' ->
      failed_nodes gst = failed_nodes gst' ->
      sigma gst = sigma gst' ->
      live_node gst = live_node gst'.
  Proof.
    intuition.
    unfold live_node.
    repeat find_rewrite.
    auto.
  Qed.

  Lemma live_node_joined : forall gst h,
      live_node gst h ->
      exists st,
        sigma gst h = Some st /\
        joined st = true.
  Proof.
    unfold live_node.
    intuition.
    break_exists_exists.
    repeat break_and.
    repeat split; auto.
  Qed.

  Lemma live_node_in_nodes : forall gst h,
      live_node gst h ->
      In h (nodes gst).
  Proof.
    unfold live_node.
    intuition.
    break_exists.
    break_and.
    auto.
  Qed.

  Lemma live_node_not_in_failed_nodes : forall gst h,
      live_node gst h ->
      ~ In h (failed_nodes gst).
  Proof.
    unfold live_node.
    intuition.
    break_exists.
    break_and.
    auto.
  Qed.

  Lemma live_node_equivalence : forall gst gst' h st st',
      live_node gst h ->
      nodes gst = nodes gst' ->
      failed_nodes gst = failed_nodes gst' ->
      Some st = sigma gst h ->
      Some st' = sigma gst' h ->
      joined st = joined st' ->
      live_node gst' h.
  Proof.
    intuition.
    break_live_node.
    eapply live_node_characterization.
    * eauto.
    * repeat find_rewrite.
      find_injection.
      eauto.
    * repeat find_rewrite; auto.
    * repeat find_rewrite; auto.
  Qed.

  Lemma apply_handler_result_preserves_nodes : forall gst gst' h res e,
      gst' = apply_handler_result h res e gst ->
      nodes gst = nodes gst'.
  Proof.
    unfold apply_handler_result.
    intuition.
    repeat break_let.
    find_rewrite; auto.
  Qed.

  Lemma apply_handler_result_preserves_failed_nodes : forall gst gst' h res e,
      gst' = apply_handler_result h res e gst ->
      failed_nodes gst = failed_nodes gst'.
  Proof.
    unfold apply_handler_result.
    intuition.
    repeat break_let.
    find_rewrite; auto.
  Qed.

  Lemma when_apply_handler_result_preserves_live_node :
    forall h h0 st st' gst gst' e ms cts nts,
      live_node gst h ->
      sigma gst h = Some st ->
      sigma gst' h = Some st' ->
      joined st' = true ->
      gst' = apply_handler_result h0 (st', ms, cts, nts) e gst ->
      live_node gst' h.
  Proof.
    intuition.
    eapply live_node_characterization.
    - eauto.
    - break_live_node.
      repeat find_rewrite.
      find_inversion; eauto.
    - find_apply_lem_hyp apply_handler_result_preserves_nodes.
      find_inversion.
      break_live_node; auto.
    - find_apply_lem_hyp apply_handler_result_preserves_failed_nodes.
      find_inversion.
      break_live_node; auto.
  Qed.

  Lemma joined_preserved_by_start_query : forall h st k st' ms nts cts,
      start_query h st k = (st', ms, nts, cts) ->
      joined st = joined st'.
  Proof.
    unfold start_query.
    intuition.
    break_match.
    - break_let.
      tuple_inversion.
      unfold update_query; auto.
    - tuple_inversion; auto.
  Qed.

  Lemma joined_preserved_by_try_rectify : forall h st st' ms ms' cts cts' nts nts',
      try_rectify h (st, ms, cts, nts) = (st', ms', cts', nts') ->
      joined st = joined st'.
  Proof.
    unfold try_rectify, clear_rectify_with.
    simpl.
    intuition.
    repeat break_match.
    - find_inversion.
      find_apply_lem_hyp joined_preserved_by_start_query; auto.
    - find_inversion; auto.
    - find_inversion; auto.
    - find_inversion; auto.
  Qed.

  Lemma joined_preserved_by_end_query : forall h st st' ms ms' cts cts' nts nts',
      end_query h (st, ms, cts, nts)  = (st', ms', cts', nts') ->
      joined st = joined st'.
  Proof.
    unfold end_query.
    intuition.
    break_match.
    - tuple_inversion; auto.
    - find_apply_lem_hyp joined_preserved_by_try_rectify; auto.
  Qed.

  Lemma joined_preserved_by_handle_stabilize : forall h src st q new_succ succ st' ms nts cts,
      handle_stabilize h src st q new_succ succ = (st', ms, nts, cts) ->
      joined st = joined st'.
  Proof.
    unfold handle_stabilize.
    unfold update_succ_list.
    intuition.
    repeat break_match.
    - find_apply_lem_hyp joined_preserved_by_start_query; auto.
    - find_apply_lem_hyp joined_preserved_by_end_query; auto.
  Qed.

  Lemma joined_preserved_by_end_query_handle_rectify : forall h st p q n st' ms nts cts,
      end_query h (handle_rectify h st p q n) = (st', ms, nts, cts) ->
      joined st = joined st'.
  Proof.
    unfold end_query.
    unfold handle_rectify.
    unfold update_pred.
    unfold update_query.
    intuition.
    repeat break_match;
      tuple_inversion;
      find_inversion || find_apply_lem_hyp joined_preserved_by_try_rectify;
      auto.
  Qed.

  (* not as strong as the other ones since handle_query for a Join query can change joined st from false to true *)
  Lemma joined_preserved_by_handle_query : forall src h st p q m st' ms nts cts,
        handle_query src h st p q m = (st', ms, nts, cts) ->
        joined st = true ->
        joined st' = true.
  Proof.
    unfold handle_query.
    unfold update_for_join.
    unfold add_tick.
    intuition.
    repeat break_match;
      try congruence;
      repeat find_reverse_rewrite.
    - find_apply_lem_hyp joined_preserved_by_end_query_handle_rectify; auto.
    - find_apply_lem_hyp joined_preserved_by_end_query; auto.
    - find_apply_lem_hyp joined_preserved_by_handle_stabilize; auto.
    - find_apply_lem_hyp joined_preserved_by_end_query; auto.
    - simpl in *.
      unfold clear_rectify_with in *.
      repeat break_match;
        try find_apply_lem_hyp joined_preserved_by_start_query;
        tuple_inversion; auto.
    - find_apply_lem_hyp joined_preserved_by_end_query; auto.
    - find_apply_lem_hyp joined_preserved_by_start_query; auto.
    - simpl in *.
      unfold clear_rectify_with in *.
      repeat break_match;
        try discriminate;
        find_injection;
        intuition;
        repeat tuple_inversion;
        auto.
  Qed.

  Lemma joined_preserved_by_recv_handler : forall src h st msg st' ms nts cts,
      recv_handler src h st msg = (st', ms, nts, cts) ->
      joined st = true ->
      joined st' = true.
  Proof.
    unfold recv_handler.
    intuition.
    repeat break_match;
      try tuple_inversion;
      eauto using joined_preserved_by_handle_query.
  Qed.

  Lemma joined_preserved_by_tick_handler : forall h st st' ms nts cts,
    tick_handler h st = (st', ms, nts, cts) ->
    joined st = joined st'.
  Proof.
    unfold tick_handler, add_tick.
    intuition.
    - repeat break_match; repeat tuple_inversion; auto.
      * repeat tuple_inversion.
        find_apply_lem_hyp joined_preserved_by_start_query; eauto.
  Qed.

  Lemma joined_preserved_by_update_pred : forall st p st',
      st' = update_pred st p ->
      joined st = joined st'.
  Proof.
    unfold update_pred.
    intuition.
    find_rewrite; auto.
  Qed.

  Lemma joined_preserved_by_handle_query_timeout : forall h st dst q st' ms nts cts,
      handle_query_timeout h st dst q = (st', ms, nts, cts) ->
      joined st = joined st'.
  Proof.
    unfold handle_query_timeout.
    intuition.
    repeat break_match;
      find_apply_lem_hyp joined_preserved_by_end_query ||
      find_apply_lem_hyp joined_preserved_by_start_query;
      eauto.
  Qed.

  Lemma joined_preserved_by_timeout_handler : forall h st t st' ms nts cts,
    timeout_handler h st t = (st', ms, nts, cts) ->
    joined st = joined st'.
  Proof.
    unfold timeout_handler.
    intuition.
    repeat break_match;
      try tuple_inversion;
      eauto using joined_preserved_by_tick_handler, joined_preserved_by_handle_query_timeout.
  Qed.

  Lemma update_fixes_other_arguments : forall f x d y,
      y <> x ->
      update f x d y = f y.
  Proof.
    unfold update.
    intuition.
    break_if; congruence.
  Qed.

  Lemma update_preserving_states : forall gst gst' h st st' o,
    sigma gst h = Some st ->
    sigma gst' = update (sigma gst) o st' ->
    h <> o ->
    sigma gst' h = Some st.
  Proof.
    intuition.
    find_reverse_rewrite.
    find_rewrite.
    apply update_fixes_other_arguments; auto.
  Qed.

  Lemma apply_handler_result_updates_sigma : forall h st ms nts cts e gst gst',
      gst' = apply_handler_result h (st, ms, nts, cts) e gst ->
      sigma gst' h = Some st.
  Proof.
    unfold apply_handler_result, update.
    intuition.
    repeat find_rewrite.
    simpl in *.
    break_if; congruence.
  Qed.

  Theorem live_node_preserved_by_recv_step : forall gst h src st msg gst' e st' ms nts cts,
      live_node gst h ->
      Some st = sigma gst h ->
      recv_handler src h st msg = (st', ms, nts, cts) ->
      gst' = apply_handler_result h (st', ms, nts, cts) e gst ->
      live_node gst' h.
  Proof.
    intuition.
    eapply when_apply_handler_result_preserves_live_node; eauto.
    - eauto using apply_handler_result_updates_sigma.
    - eapply joined_preserved_by_recv_handler.
      * eauto.
      * break_live_node.
        find_rewrite.
        find_injection.
        auto.
  Qed.

  Theorem live_node_preserved_by_timeout_step : forall gst h st st' t ms nts cts e gst',
      live_node gst h ->
      sigma gst h = Some st ->
      timeout_handler h st t = (st', ms, nts, cts) ->
      gst' = apply_handler_result h (st', ms, nts, t :: cts) e gst ->
      live_node gst' h.
  Proof.
    intuition.
    eapply when_apply_handler_result_preserves_live_node; eauto.
    - eauto using apply_handler_result_updates_sigma.
    - break_live_node.
      find_apply_lem_hyp joined_preserved_by_timeout_handler.
      repeat find_rewrite.
      find_injection.
      eauto.
  Qed.

  Lemma adding_nodes_does_not_affect_live_node : forall gst gst' h n st,
      ~ In n (nodes gst) ->
      sigma gst' = update (sigma gst) n st ->
      nodes gst' = n :: nodes gst ->
      failed_nodes gst' = failed_nodes gst ->
      live_node gst h ->
      live_node gst' h.
  Proof.
    intuition.
    unfold live_node.
    break_live_node_exists_exists.
    repeat split.
    * eapply update_preserving_states; eauto.
      congruence.
    * auto.
    * find_rewrite.
      eauto using in_cons.
    * find_rewrite.
      auto.
  Qed.

  (* reverse of the above, with additional hypothesis that h <> n. *)
  Lemma adding_nodes_did_not_affect_live_node : forall gst gst' h n st,
      ~ In n (nodes gst) ->
      sigma gst' = update (sigma gst) n st ->
      nodes gst' = n :: nodes gst ->
      failed_nodes gst' = failed_nodes gst ->
      live_node gst' h ->
      h <> n ->
      live_node gst h.
  Proof.
    intuition.
    unfold live_node.
    break_live_node_exists_exists.
    repeat split.
    * repeat find_reverse_rewrite.
      find_rewrite.
      find_rewrite.
      find_rewrite.
      find_rewrite.
      symmetry.
      apply update_fixes_other_arguments.
      congruence.
    * auto.
    * repeat find_rewrite.
      find_apply_lem_hyp in_inv.
      break_or_hyp; congruence.
    * find_rewrite; auto.
  Qed.

  Lemma adding_nodes_does_not_affect_dead_node : forall gst gst' h n st,
      ~ In n (nodes gst) ->
      sigma gst' = update (sigma gst) n st ->
      nodes gst' = n :: nodes gst ->
      failed_nodes gst' = failed_nodes gst ->
      dead_node gst h ->
      dead_node gst' h.
  Proof.
    intuition.
    break_dead_node.
    unfold dead_node.
    eexists.
    repeat split.
    - eapply update_preserving_states; eauto.
      congruence.
    - find_rewrite.
      eauto using in_cons.
    - find_rewrite; auto.
  Qed.

  Lemma adding_nodes_does_not_affect_best_succ : forall gst gst' h s n st,
      best_succ gst h s ->
      ~ In n (nodes gst) ->
      sigma gst' = update (sigma gst) n st ->
      nodes gst' = n :: nodes gst ->
      failed_nodes gst' = failed_nodes gst ->
      best_succ gst' h s.
  Proof.
    unfold best_succ.
    intuition.
    break_exists_exists.
    repeat split; break_and.
    - eauto using adding_nodes_does_not_affect_live_node.
    - eapply update_preserving_states; eauto.
      repeat break_live_node.
      congruence.
    - auto.
    - intuition.
      find_copy_apply_hyp_hyp.
      break_dead_node.
      eapply adding_nodes_does_not_affect_dead_node; eauto.
    - eauto using adding_nodes_does_not_affect_live_node.
  Qed.

  Lemma adding_node_preserves_reachable : forall h from to gst gst' st,
        reachable gst from to ->
        ~ In h (nodes gst) ->
        nodes gst' = h :: nodes gst ->
        failed_nodes gst' = failed_nodes gst ->
        sigma gst' = update (sigma gst) h st ->
        reachable gst' from to.
  Proof.
    intuition.
    induction H.
    - apply ReachableSucc.
      eauto using adding_nodes_does_not_affect_best_succ.
    - eauto using ReachableTransL, adding_nodes_does_not_affect_best_succ.
  Qed.

  Theorem start_step_keeps_at_least_one_ring : forall h gst gst' st known k,
        at_least_one_ring gst ->
        ~ In h (nodes gst) ->
        (In k known -> In k (nodes gst)) ->
        (In k known -> ~ In k (failed_nodes gst)) ->
        (known = [] -> nodes gst = []) ->
        nodes gst' = h :: nodes gst ->
        failed_nodes gst' = failed_nodes gst ->
        sigma gst' = update (sigma gst) h st ->
        at_least_one_ring gst'.
  Proof.
    unfold at_least_one_ring, ring_member.
    intuition.
    break_exists_exists.
    eauto using adding_node_preserves_reachable.
  Qed.

  Theorem invariant_steps_to_at_least_one_ring : forall gst gst',
      inductive_invariant gst ->
      step_dynamic gst gst' ->
      at_least_one_ring gst'.
  Proof.
    intuition.
    break_invariant.
    break_step.
    - eapply start_step_keeps_at_least_one_ring; simpl; eauto.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Theorem invariant_steps_to_at_most_one_ring : forall gst gst',
      inductive_invariant gst ->
      step_dynamic gst gst' ->
      at_most_one_ring gst'.
  Admitted.

  Theorem invariant_steps_to_ordered_ring : forall gst gst',
      inductive_invariant gst ->
      step_dynamic gst gst' ->
      ordered_ring gst'.
  Admitted.

  Theorem invariant_steps_to_connected_appendages : forall gst gst',
      inductive_invariant gst ->
      step_dynamic gst gst' ->
      connected_appendages gst'.
  Admitted.

  Theorem invariant_steps_to_base_not_skipped : forall gst gst',
      inductive_invariant gst ->
      step_dynamic gst gst' ->
      base_not_skipped gst'.
  Admitted.

  Theorem invariant_is_invariant : forall gst gst',
      inductive_invariant gst ->
      step_dynamic gst gst' ->
      inductive_invariant gst'.
  Proof.
    intuition.
    unfold inductive_invariant.
    repeat split.
    - eauto using invariant_steps_to_at_least_one_ring.
    - eauto using invariant_steps_to_at_most_one_ring.
    - eauto using invariant_steps_to_ordered_ring.
    - eauto using invariant_steps_to_connected_appendages.
    - eauto using invariant_steps_to_base_not_skipped.
  Qed.

End ChordProof.