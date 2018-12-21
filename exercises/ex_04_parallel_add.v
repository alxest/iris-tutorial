(**
In this exercise we use the spin-lock from the previous exercise to implement
the running example during the lecture of the tutorial: proving that when two
threads increase a reference that's initially zero by two, the result is four.
*)
From iris.algebra Require Import auth frac_auth.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import lib.par proofmode notation.
From tutorial Require Import ex_03_spinlock.

Print heap_lang.
Eval simpl in (@language.prim_step heap_lang).

Ltac wp_exec := repeat (wp_pure _ || wp_load || wp_store).

(** The program as a heap-lang expression. We use the heap-lang [par] module for
parallel composition. *)
Definition parallel_add : expr :=
  let: "r" := ref #0 in
  let: "l" := newlock #() in
  (
    (acquire "l";; "r" <- !"r" + #2;; release "l")
  |||
    (acquire "l";; "r" <- !"r" + #2;; release "l")
  );;
  acquire "l";;
  !"r".

(** 1st proof : we only prove that the return value is even.
No ghost state is involved in this proof. *)
Section proof1.
  Context `{!heapG Σ, !spawnG Σ}.

  Definition parallel_add_inv_1 (r : loc) : iProp Σ :=
    (∃ n : Z, r ↦ #n ∗ ⌜ Zeven n ⌝)%I.

  (** *Exercise*: finish the missing cases of this proof. *)
  Lemma parallel_add_spec_1 :
    {{{ True }}} parallel_add {{{ n, RET #n; ⌜Zeven n⌝ }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add. wp_alloc r as "Hr". wp_let.
    wp_apply (newlock_spec (parallel_add_inv_1 r) with "[Hr]").
    { (* exercise *)
      unfold parallel_add_inv_1. iExists _. iFrame.
    }
    iIntros (l) "#Hl". wp_let.
    (* Q: How does the concept of "logically atomic" (in iris 1.0) appear? *)
    (* Iris 3.0
Notice, however, that the base logic does not have a notion of “threads” or “programs”,
but only of
separation
. Ultimately, the logic does not care about “who” owns the resources
under consideration; it is only concerned with reasoning about consequences of ownership
and how it can be merged and split disjointly. 
     *)
    About wp_par.
    Goal 
∀ (Σ : gFunctors) (heapG0 : heapG Σ), spawnG Σ
                                      → ∀ (Ψ1 Ψ2 : val → iProp Σ) (e1 e2 : expr) (Φ : val → iProp Σ), 
                                      WP e1 {{ v, Ψ1 v }}
                                      -∗ WP e2 {{ v, Ψ2 v }}
                                         -∗ (∀ v1 v2 : val, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (v1, v2)%V)
                                            -∗ WP e1 ||| e2 {{ v, Φ v }}.
Proof.
  intros.
  iIntros.
Abort.
    wp_apply (par_spec (λ _, True%I) (λ _, True%I)).
    (* wp_apply (wp_par (λ _, True%I) (λ _, True%I)). *)
    - wp_apply (acquire_spec with "Hl"). iDestruct 1 as (n) "[Hr %]".
      wp_seq. wp_load. wp_op. wp_store.
      wp_apply (release_spec with "[Hr $Hl]"); [|done].
      iExists _. iFrame "Hr". iPureIntro. by apply Zeven_plus_Zeven.
    - (* exercise *)
      wp_apply (acquire_spec with "Hl"). iDestruct 1 as (n) "[Hr %]".
      Local Opaque release.
      wp_exec.
      Local Transparent release.
      wp_apply (release_spec); eauto. Undo 1. (* we lost "Hr" *)
      iApply (release_spec with "[Hr]").
      + iSplit; eauto.
        unfold parallel_add_inv_1. iExists _. iSplit; eauto.
        iPureIntro. apply Zeven_plus_Zeven; auto. econstructor.
      + eauto.
    - (* exercise *)
      iIntros.
      iNext.
      wp_seq.
      wp_apply (acquire_spec with "Hl"). iDestruct 1 as (n) "[Hr %]".
      wp_exec. iApply "Post". eauto.
  Qed.

End proof1.

(** 2nd proof : we prove that the program returns 4 exactly.
We need a piece of ghost state: integer ghost variables.

Whereas we previously abstracted over an arbitrary "ghost state" [Σ] in the
proofs, we now need to make sure that we can use integer ghost variables. For
this, we add the type class constraint:

  inG Σ (authR (optionUR (exclR ZC)))

*)

Section proof2.
  Context `{!heapG Σ, !spawnG Σ, !inG Σ (authR (optionUR (exclR ZC)))}.

  Definition parallel_add_inv_2 (r : loc) (γ1 γ2 : gname) : iProp Σ :=
    (∃ n1 n2 : Z, r ↦ #(n1 + n2)
            ∗ own γ1 (● (Excl' n1)) ∗ own γ2 (● (Excl' n2)))%I.

  (** Some helping lemmas for ghost state that we need in the proof. In actual
  proofs we tend to inline simple lemmas like these, but they are here to
  make things easier to understand. *)
  Lemma ghost_var_alloc n :
    (|==> ∃ γ, own γ (● (Excl' n)) ∗ own γ (◯ (Excl' n)))%I.
  Proof.
    iMod (own_alloc (● (Excl' n) ⋅ ◯ (Excl' n))) as (γ) "[??]"; by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree γ n m :
    own γ (● (Excl' n)) -∗ own γ (◯ (Excl' m)) -∗ ⌜ n = m ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iDestruct (own_valid_2 with "Hγ● Hγ◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_valid_discrete_2.
  Qed.

  Lemma ghost_var_update γ n' n m :
    own γ (● (Excl' n)) -∗ own γ (◯ (Excl' m)) ==∗
      own γ (● (Excl' n')) ∗ own γ (◯ (Excl' n')).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' n' ⋅ ◯ Excl' n') with "Hγ● Hγ◯") as "[$$]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    done.
  Qed.

  (** *Exercise*: finish the missing cases of the proof. *)
  Lemma parallel_add_spec_2 :
    {{{ True }}} parallel_add {{{ RET #4; True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add. wp_alloc r as "Hr". wp_let.
    iMod (ghost_var_alloc 0) as (γ1) "[Hγ1● Hγ1◯]".
    iMod (ghost_var_alloc 0) as (γ2) "[Hγ2● Hγ2◯]".
    wp_apply (newlock_spec (parallel_add_inv_2 r γ1 γ2) with "[Hr Hγ1● Hγ2●]").
    { (* exercise *)
      unfold parallel_add_inv_2.
      iExists _, _.
      iFrame.
    }
    iIntros (l) "#Hl". wp_let.
    (**********************************************)
    (* ownership of ghost resources are splitted! *)
    (**********************************************)
    wp_apply (par_spec (λ _, own γ1 (◯ Excl' 2)) (λ _, own γ2 (◯ Excl' 2))
                with "[Hγ1◯] [Hγ2◯]").
    (* wp_apply (wp_par (λ _, own γ1 (◯ Excl' 2)) (λ _, own γ2 (◯ Excl' 2)) *)
    (*             with "[Hγ1◯] [Hγ2◯]"). *)
    - wp_apply (acquire_spec with "Hl"). iDestruct 1 as (n1 n2) "(Hr & Hγ1● & Hγ2●)".
      wp_seq. wp_load. wp_op. wp_store.
      iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->.
      iMod (ghost_var_update γ1 2 with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]".
      wp_apply (release_spec with "[- $Hl Hγ1◯]"); [|by auto].
      iExists _, _. iFrame "Hγ1● Hγ2●". rewrite (_ : 2 + n2 = 0 + n2 + 2); [done|ring].
    - (* exercise *)
      wp_apply (acquire_spec); eauto.
      iDestruct 1 as (n1 n2) "(Hr & Hγ1● & Hγ2●)".
      wp_seq. wp_load. wp_op. wp_store.
      iDestruct (ghost_var_agree with "Hγ2● Hγ2◯") as %->.
      iMod (ghost_var_update γ2 2 with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".
      wp_apply (release_spec with "[Hr Hγ1● Hγ2●]"); cycle 1.
      {
        Fail iMod (ghost_var_update γ2 2 with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]". (* ?????????? *)
        eauto.
      }
      iSplit; eauto.
      unfold parallel_add_inv_2.
      iExists _, _. iFrame.
      replace (n1 + 2) with (n1 + 0 + 2); eauto.
      omega.
    - (* exercise *)
      iIntros (v1 v2) "OWN".
      iNext.
      wp_seq.
      wp_apply (acquire_spec with "Hl"). iDestruct 1 as (n1 n2) "(Hr & Hγ1● & Hγ2●)".
      iDestruct "OWN" as "[Hγ1◯ Hγ2◯]".
      iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->.
      iDestruct (ghost_var_agree with "Hγ2● Hγ2◯") as %->.
      wp_exec.
      change (2 + 2) with 4.
      iApply "Post".
      eauto.
  Qed.

  Lemma parallel_add_spec_2_weird :
    {{{ True }}} parallel_add {{{ RET #4; True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add. wp_alloc r as "Hr". wp_let.
    iMod (ghost_var_alloc 0) as (γ1) "[Hγ1● Hγ1◯]".
    iMod (ghost_var_alloc 0) as (γ2) "[Hγ2● Hγ2◯]".
    wp_apply (newlock_spec (parallel_add_inv_2 r γ1 γ2) with "[Hr Hγ1● Hγ2●]").
    { (* exercise *)
      unfold parallel_add_inv_2.
      iExists _, _.
      iFrame.
    }
    iIntros (l) "#Hl". wp_let.
    wp_apply (par_spec (λ _, own γ1 (◯ Excl' 777)) (λ _, own γ2 (◯ Excl' 777))
                with "[Hγ1◯] [Hγ2◯]").
    (* wp_apply (wp_par (λ _, own γ1 (◯ Excl' 777)) (λ _, own γ2 (◯ Excl' 777)) *)
    (*             with "[Hγ1◯] [Hγ2◯]"). *)
    - wp_apply (acquire_spec with "Hl"). iDestruct 1 as (n1 n2) "(Hr & Hγ1● & Hγ2●)".
      wp_seq. wp_load. wp_op. wp_store.
      iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->.
      iMod (ghost_var_update γ1 777 with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]".
      wp_apply (release_spec with "[- $Hl Hγ1◯]"); [|by auto].
      iExists _, _. iFrame "Hγ1● Hγ2●".
  Abort.

End proof2.

(** 3rd proof : we prove that the program returns 4 exactly, but using a
fractional authoritative ghost state.  We need another piece of ghost state. *)
Section proof3.
  Context `{!heapG Σ, !spawnG Σ, !inG Σ (frac_authR natR)}.

  Definition parallel_add_inv_3 (r : loc) (γ : gname) : iProp Σ :=
    (∃ n : nat, r ↦ #n ∗ own γ (●! n))%I.
  (* Definition parallel_add_inv_2 (r : loc) (γ1 γ2 : gname) : iProp Σ := *)
  (*   (∃ n1 n2 : Z, r ↦ #(n1 + n2) *)
  (*           ∗ own γ1 (● (Excl' n1)) ∗ own γ2 (● (Excl' n2)))%I. *)


  (** *Exercise*: finish the missing cases of the proof. *)
  Lemma parallel_add_spec_3 :
    {{{ True }}} parallel_add {{{ RET #4; True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add. wp_alloc r as "Hr". wp_let.
    iMod (own_alloc (●! 0%nat ⋅ ◯! 0%nat)) as (γ) "[Hγ● [Hγ1◯ Hγ2◯]]"; [done|].
    wp_apply (newlock_spec (parallel_add_inv_3 r γ) with "[Hr Hγ●]").
    { (* exercise *)
      unfold parallel_add_inv_3.
      iExists _. iFrame.
    }
    iIntros (l) "#Hl". wp_let.
    wp_apply (par_spec (λ _, own γ (◯!{1/2} 2%nat)) (λ _, own γ (◯!{1/2} 2%nat))
                with "[Hγ1◯] [Hγ2◯]").
    (* wp_apply (wp_par (λ _, own γ (◯!{1/2} 2%nat)) (λ _, own γ (◯!{1/2} 2%nat)) *)
    (*             with "[Hγ1◯] [Hγ2◯]"). *)
    - wp_apply (acquire_spec with "Hl"). iDestruct 1 as (n) "[Hr Hγ●]".
      wp_seq. wp_load. wp_op. wp_store.
      iMod (own_update_2 _ _ _ (●! (n+2) ⋅ ◯!{1/2}2)%nat with "Hγ● Hγ1◯") as "[Hγ● Hγ1◯]".
      { rewrite (comm plus).
        by apply frac_auth_update, (op_local_update_discrete n 0 2)%nat. }
      wp_apply (release_spec with "[$Hl Hr Hγ●]"); [|by auto].
      iExists _. iFrame. by rewrite Nat2Z.inj_add.
    - (* exercise *)
      wp_apply (acquire_spec); eauto.
      iDestruct 1 as (n) "[LOC OWN]".
      wp_seq. wp_load. wp_op. wp_store.
      iMod (own_update_2 _ _ _ (●! (n+2) ⋅ ◯!{1/2}2)%nat with "OWN Hγ2◯") as "[OWN Hγ2◯]".
      { rewrite (comm plus).
        by apply frac_auth_update, (op_local_update_discrete n 0 2)%nat. }
      (* iDestruct (ghost_var_agree with "Hγ2● Hγ2◯") as %->. *)
      (* iMod (ghost_var_update γ2 2 with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]". *)
      wp_apply (release_spec with "[LOC OWN]"); cycle 1.
      {
        iIntros.
        Print frac_auth.
        Print lib.own.
        eauto.
      }
      iSplit; eauto.
      unfold parallel_add_inv_3.
      iExists _. iFrame.
      rewrite Nat2Z.inj_add. auto.
    - (* exercise *)
      iIntros (v1 v2) "[A B]".
      iNext.
      wp_seq.
      wp_apply (acquire_spec); eauto.
      iDestruct 1 as (n) "[LOC OWN]".
      wp_exec.

      iCombine "A B" as "OWN0".
      iDestruct (own_valid_2 with "OWN OWN0") as %->%frac_auth_agreeL.
      by iApply "Post".
  Qed.

End proof3.
