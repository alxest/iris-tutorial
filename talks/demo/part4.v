From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.
From iris.algebra Require Import frac_auth.
Local Definition N := nroot .@ "example".

(* PART 4: Parellel increment (from JH's talk) *)
Definition par_inc : val := λ: <>,
  let: "l" := ref #0 in
  (FAA "l" #2 ||| FAA "l" #2);;
  !"l".

Section proof1.
  Context `{heapG Σ, spawnG Σ}.

  Lemma Zeven_2 : Zeven 2.
  Proof. done. Qed.
  Hint Resolve Zeven_2 Zeven_plus_Zeven.

  Lemma par_inc_even_spec :
    {{{ True }}} par_inc #() {{{ n, RET #n; ⌜ Zeven n ⌝ }}}.
  Proof.
    iIntros (Φ) "_ Post". wp_lam. wp_alloc l as "Hl". wp_let.
    iMod (inv_alloc N _ (∃ n : Z, l ↦ #n ∧ ⌜ Zeven n ⌝)%I with "[Hl]") as "#?".
    { iExists 0. auto. }
    wp_bind (_ ||| _)%E.
    (* wp_apply (wp_par (λ _, True)%I (λ _, True)%I). *)
    wp_apply (par_spec (λ _, True)%I (λ _, True)%I).
    - wp_lam. iInv N as (n) ">[Hl %]" "Hclose".
      wp_faa. iMod ("Hclose" with "[Hl]"); first eauto 10.
      auto.
    - wp_lam. iInv N as (n) ">[Hl %]" "Hclose".
      wp_faa. iMod ("Hclose" with "[Hl]"); first eauto 10.
      auto.
    - iIntros (v1 v2) "_". iNext. wp_seq.
      iInv N as (n) ">[Hl %]" "Hclose".
      wp_load. iMod ("Hclose" with "[Hl]"); first eauto 10.
      iApply "Post"; auto.
  Qed.
End proof1.

(* PART 5: Better parellel increment *)
Definition par_incN_helper : val :=
  rec: "helper" "n" "l" :=
    if: "n" = #0 then #()
    else (FAA "l" #2 ||| "helper" ("n" - #1) "l").
Definition par_incN : val := λ: "n",
  let: "l" := ref #0 in
  par_incN_helper "n" "l";;
  !"l".

Section proof2.
  Context `{heapG Σ, spawnG Σ, inG Σ (frac_authR natR)}.
  Implicit Types n : nat.

  (* Rules for fractional ghost variables
     (proved from generic principles) *)
  Lemma frac_auth_alloc n :
    (|==> ∃ γ, own γ (●! n) ∗ own γ (◯!{1} n))%I.
  Proof.
    by iMod (own_alloc (●! n ⋅ ◯! n))
      as (γ) "[??]"; eauto with iFrame.
  Qed.

  Lemma frac_auth_update n n1 n2 q γ :
    own γ (●! n1) -∗
    own γ (◯!{q} n2) -∗ |==>
    own γ (●! (n1 + n)%nat) ∗ own γ (◯!{q} (n2 + n)%nat).
  Proof.
    iIntros "H H'". iMod (own_update_2 with "H H'") as "[$ $]"; last done.
    apply frac_auth_update, nat_local_update. lia.
  Qed.

  Lemma frac_auth_agree n n' γ :
    own γ (●! n) -∗ own γ (◯!{1} n') -∗ ⌜n = n'⌝.
  Proof.
    iIntros "H H'".
    by iDestruct (own_valid_2 with "H H'") as %->%frac_auth_agreeL.
  Qed.

  (* The invariant that we use *)
  Definition proof2_inv (γ : gname) (l : loc) : iProp Σ :=
    (∃ n : nat, own γ (●! n) ∗ l ↦ #n)%I.

  (* Proof of the threads *)
  Lemma par_inc_FAA_spec n n' γ l q :
    {{{ inv N (proof2_inv γ l) ∗ own γ (◯!{q} n) }}}
      FAA #l #n'
    {{{ m, RET #m; own γ (◯!{q} (n + n'))%nat }}}.
  Proof.
    iIntros (Φ) "[#Hinv Hγ] Post". iInv N as (m) ">[Hauth Hl]" "Hclose".
    wp_faa.
    iMod (frac_auth_update n' with "Hauth Hγ") as "[Hauth Hγ]".
    iMod ("Hclose" with "[Hauth Hl]") as "_".
    { iNext; iExists (m + n')%nat. rewrite Nat2Z.inj_add. iFrame. }
    by iApply "Post".
  Qed.

  (* Proof of the whole program *)
  Lemma par_inc_spec :
    {{{ True }}} par_inc #() {{{ RET #4%nat; True }}}.
  Proof.
    iIntros (Φ) "_ Post". wp_lam. wp_alloc l as "Hl". wp_let.
    iMod (frac_auth_alloc 0) as (γ) "[Hauth Hγ]".
    iDestruct "Hγ" as "[Hγ1 Hγ2]".
    iMod (inv_alloc _ _ (proof2_inv γ l) with "[Hl Hauth]") as "#Hinv".
    { iNext. iExists 0%nat. iFrame. }
    wp_apply (par_spec (λ _, own γ (◯!{1/2} 2%nat))
                     (λ _, own γ (◯!{1/2} 2%nat)) with "[Hγ1] [Hγ2]").
    - wp_lam. iApply (par_inc_FAA_spec 0 2 with "[$]"); auto.
    - wp_lam. iApply (par_inc_FAA_spec 0 2 with "[$]"); auto.
    - iIntros (v1 v2) "[Hγ1 Hγ2] !>". iCombine "Hγ1 Hγ2" as "Hγ". simpl.
      wp_seq. iInv N as (m) ">[Hauth Hx]" "Hclose".
      iDestruct (frac_auth_agree with "Hauth Hγ") as %->.
      wp_load.
      iMod ("Hclose" with "[Hauth Hx]") as "_".
      { iNext. iExists 4%nat. iFrame. }
      by iApply "Post".
  Qed.

  Lemma par_incN_helper_spec n γ l q :
    {{{ inv N (proof2_inv γ l) ∗ own γ (◯!{q} 0%nat) }}}
      par_incN_helper #n #l
    {{{ v, RET v; own γ (◯!{q} (n * 2))%nat }}}.
  Proof.
    iIntros (Φ) "[#? Hγ] Post /=".
    iInduction n as [|n] "IH" forall (q Φ).
    { wp_lam. wp_let. wp_op. wp_if. by iApply "Post". }
    rewrite Nat2Z.inj_succ. do 2 (wp_lam + wp_let).
    wp_op. case_bool_decide; first lia. wp_if.
    iDestruct "Hγ" as "[Hγ1 Hγ2]".
    wp_apply (wp_par (λ _, own γ (◯!{q/2} 2%nat))
                     (λ _, own γ (◯!{q/2} (n * 2)%nat)) with "[Hγ1] [Hγ2]").
    - iApply (par_inc_FAA_spec 0 2 with "[$]"); auto.
    - wp_op. rewrite (_ : Z.succ n - 1 = n); last lia.
      iApply ("IH" with "Hγ2"); auto.
    - iIntros (v1 v2) "[Hγ1 Hγ2] !>". iCombine "Hγ1 Hγ2" as "Hγ".
      by iApply "Post".
  Qed.

  Lemma par_incN_spec n :
    {{{ True }}} par_incN #n {{{ RET #(n * 2)%nat; True }}}.
  Proof.
    iIntros (Φ) "_ Post". wp_lam. wp_alloc l as "Hl". wp_let.
    iMod (frac_auth_alloc 0) as (γ) "[Hauth Hγ]".
    iMod (inv_alloc _ _ (proof2_inv γ l) with "[Hl Hauth]") as "#Hinv".
    { iNext. iExists 0%nat. iFrame. }
    wp_apply (par_incN_helper_spec with "[$]").
    iIntros (v) "Hγ". wp_seq.
    iInv N as (m) ">[Hauth Hx]" "Hclose".
    iDestruct (frac_auth_agree with "Hauth Hγ") as %->.
    wp_load.
    iMod ("Hclose" with "[Hauth Hx]") as "_".
    { iNext. iExists (n * 2)%nat. iFrame. }
    by iApply "Post".
  Qed.
End proof2.
