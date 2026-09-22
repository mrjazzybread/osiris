From osiris Require Import osiris.
From osiris.stdlib Require Import Externals Stdlib.

(* The deep embedding obtained from translating [queue.ml]. *)
From osiris.stdlib Require Import og_queue.

(* Boilerplate pertaining to the [cell] and [t] types. *)

Section boilerplate.

  Inductive cell : Type :=
  | Nil
  | Cons (r : record).

  Global Instance record_eq_dec : EqDecision record.
  Proof. solve_decision. Qed.

  Global Instance cell_eq_dec : EqDecision cell.
  Proof. solve_decision. Qed.

  Record cons `{Encode A} := { content : A; next : cell }.

  Record t := { length : Z; first : cell; last : cell }.

  Global Instance encode_cell : Encode cell :=
    { encode' c := match c with
                   | Nil => VConstant "Nil"
                   | Cons r => VInline "Cons" r
                   end }.

  Global Instance Constant_Nil : Constant "Nil" cell :=
    { constant_value := Nil; constant_encode := eq_refl }.

  Global Instance cons_repr `{Encode A} : RecordRepr (@cons A _) τ[A; cell] Mut :=
    { repr_to_types c := (c.(content), c.(next));
      types_to_repr := λ c n, {| content := c; next := n |};
      repr_id := λ '(c, n), eq_refl }.

  Global Instance cons_inline : Inline "Cons" cell := {| inline_apply := Cons;
                                                        inline_encode := λ _, eq_refl |}.

  Global Instance t_repr : RecordRepr t τ[Z; cell; cell] Mut :=
    { repr_to_types t := (t.(length), (t.(first), t.(last)));
      types_to_repr := λ l fst lst, {| length := l; first := fst; last := lst |};
      repr_id := λ '(l, (fst, lst)), eq_refl }.

End boilerplate.

(* The [Cell], [Cell_Seg], and [Queue] resources.  *)

Section queue_resources.

  Context `{!osirisGS Σ}.

  Definition Cell `{Encode A} (c n : cell) (v : A) : iProp Σ :=
    ∃ r,
      ⌜c = Cons r⌝ ∗ r ⤇ {| content := v; next := n |}.

  Fixpoint Cell_Seg `{Encode A} (from to : cell) (l : list A) : iProp Σ :=
    match l with
    | [] => ⌜to = from⌝
    | x :: l' => ∃ n, Cell from n x ∗ Cell_Seg n to l'
    end.

  Definition Queue `{Encode A} (q : record) (l : list A) : iProp Σ :=
    ∃ (cf cl : cell),
      q ⤇ {| length := list_z.length l; first := cf; last := cl |} ∗
      if decide (l = nil) then
        ⌜cf = Nil⌝ ∗ ⌜cl = Nil⌝
      else
        ∃ x l',
          ⌜ l = l' ++ [x] ⌝ ∗
          Cell_Seg cf cl l' ∗ Cell_Seg cl Nil [x].

  Lemma Cell_Seg_app A `{Encode A} r (x' : A) c cf l:
      r ⤇ {| content := x'; next := c |} -∗
      Cell_Seg cf (Cons r) l -∗
      Cell_Seg cf c (l ++ [x']).
  Proof.
    iIntros "C S".
    iInduction l as [|h t Ih] forall (cf c).
    - simpl. iDestruct "S" as "<-". by iFrame.
    - simpl. iDestruct "S" as "(% & ? & S)".
      iFrame. iApply ("Ih" with "[$] [$]").
  Qed.

End queue_resources.

(* This section contains the proofs of the functions.
   We work with weakest preconditions rather than triples. *)

(* Functions which call other functions should have an assumption that
   those other functions are in-scope.

   These assumptions are written [□ in_env "name" spec η], examples can
   be found in 'array.v', e.g. in [imp_init]. *)

Section proofs.

  Context `{!osirisGS Σ}.

  (* We specify functions in the following way:
     [iSpec τ[...] f f_spec] says that [f] is a function with arguments
     of type [...] and with specification [f_spec].

     [f_spec] should have type [... → microvx → iProp Σ], where
     [m : microvx] is the call-site of the function to the arguments. *)

  (* For create, we have one argument of type [unit], and the
     specification is for any type, we get [q] an empty queue with
     elements of that type. *)

  Definition create_spec (u : unit) (m : microvx) : iProp Σ :=
    ∀ A (HencA : Encode A), EWP m {{ q, Queue q (@nil A) }}.

  Definition create := (EAnonFun __create).

  (* Because our language has words of arbitrary size, we need to
     assume that the words are big enough to index all of the fields of
     [t] records. *)
  Hypothesis max_fields : 3 ≤ max_array_length.

  Lemma imp_create η :
    ⊢ EWP (eval η create) {{ f, □ iSpec τ[unit] f create_spec }}.
  Proof.
    (* [imp_EAnon_pers] is the lemma for proving that a function
       persistently satisfies its specification. *)
    iApply imp_EAnon_pers.
    iIntros "!> /=". unfold create_spec.
    iIntros ([] A HencA).
    iApply imp_please; iNext.

    (* The [()] argument binding acts as a match on the first argument *)
    imp_match unit. rewrite -encode_encode'.

    imp_record.
    simpl.
    iIntros (v) "(%l & %cf & %cl & Hv & -> & -> & ->)".
    unfold Queue. by iFrame.
  Qed.

  Definition add_spec {A} `{Encode A} (x : A) (_q : record) (m : microvx) : iProp Σ :=
    ∀ (q : list A),
      ▷ Queue _q q -∗
      EWP m {{ (), Queue _q (q ++ [x]) }}.

  Definition add := (EAnonFun __add).

  Lemma imp_add η A `(Encode A) :
    ⊢ EWP (eval η add) {{ f, □ iSpec τ[A;record] f add_spec }}.
  Proof.
    iApply imp_EAnon_pers. unfold add_spec.
    iIntros "!> /= %x %q %l Hq".
    iApply imp_please; iNext.
    imp_let $! (λ (c : cell), Cell c Nil x).
    { imp_record $! (cons (A:=A)). simpl.
        iIntros "% (% & -> & (% & % & ? & -> & ->))".
        by iFrame. }
    iIntros "%c C".
    iDestruct "Hq" as "(%cf & %cl& Ql & Q)".
    imp_match cell with "[Ql]".
    iIntros "(-> & Ql)". simpl.
    destruct l as [|h t].
    - iDestruct "Q" as "[-> ->]".
      next_branch.
      iApply (imp_ESeq with "[Ql]").
      iApply (imp_record_update with "Ql").
      { split; simpl; lia. }
      { imp_path. }
      { imp_int. }
      { rewrite -encode_encode'.
        simpl. iIntros "(%_ & -> & Ql)".
        iApply (imp_ESeq with "[Ql]").
        iApply (imp_record_update with "Ql");
          try imp_path.
        { split; simpl; lia. }
        simpl. iIntros "(%_ & -> & Ql)".
        iApply (imp_wand with "[-]").
        iApply (imp_record_update with "Ql").
        { split; simpl; lia. }
        { imp_path. }
        { set_postcondition
            (λ c', Cell c' Nil x ∗ ⌜ c = c'⌝)%I.
          imp_path.
          by iFrame. }
        simpl. iIntros "% (% & (? & <-) & ?)".
        destruct v. iUnfold Queue.
        iFrame. by iExists []. }
    -
      iDestruct "Q" as "(%x' & %l & -> & S & % & Cl & <-)".
      iDestruct "Cl" as "(%r & -> & Cl)".
      rewrite !(encode_encode' (A:=cell)).
      rewrite <- (encode_encode' (A:=cell)).
      next_branch.
      next_branch.
      iApply (imp_ESeq with "[Ql]").
      {  set_postcondition (λ _, q ⤇ _)%I.
         iApply (imp_record_update' with "[] [Ql]").
      { split; simpl; lia. }
      { imp_path. }
      { imp_arith reading "Ql". iFrame "Ql".
        imp_int. }
      { simpl. iIntros "% (-> & $)".
        iIntros "!>$". } }
      simpl. iIntros "Ql".
      iApply (imp_ESeq with "[Cl]").
      iApply (imp_record_update with "Cl").
      { split; simpl; lia. }
      { imp_path. }
      { imp_path. }
      simpl. iIntros "(% & [-> Cl])".
      iApply (imp_wand with "[Ql]").
      iApply (imp_record_update with "Ql").
      { split; simpl; lia. }
      { imp_path. }
      { imp_path. }
      simpl. iIntros ([]) "(% & [-> Ql])".
      iUnfold Queue.
      list_z.length. iFrame "Ql".
      rewrite decide_False.
      2: { destruct l; discriminate. }
      iExists x, (l ++ [x']).
      iFrame. repeat iSplit; try done.
      iApply (Cell_Seg_app with "[$] [$]").
  Qed.

End proofs.

(* After having proven all the functions individually, we want to prove
   that the whole module is correct.

   A module specification (currently called [context]) asserts the
   domain of the module, and specifications for a subset of the domain. *)

Section module_proof.

  Context `{!osirisGS Σ}.

  Definition queue_module_dom : gset var :=
    {[ "Empty";
       "create";
       "clear";
       "add";
       "push";
       "peek";
       "peek_opt";
       "top";
       "take";
       "take_opt";
       "pop";
       "copy";
       "is_empty";
       "length";
       "iter";
       "fold";
       "transfer";
       "to_seq";
       "add_seq";
       "of_seq"
     ]}.

  Definition queue_module_spec : env → iProp Σ :=
    (context [
       var_spec "create" (λ create, □ iSpec τ[unit] create create_spec)
     ]
     queue_module_dom)%I.

  Local Notation "'next_top:' sitem" :=
    (impure ⊤ (eval_sitems _ (sitem :: _)) ⊥ ⊥ _) (at level 20).

  Hypothesis max_fields : 3 ≤ max_array_length.

  (* The proof of the whole module. *)

  Lemma module_proof η :
    ⊢ EWP (eval_mexpr η __main) {{ queue_module_spec }}.
  Proof.
    iApply imp_module.
    iApply imp_sitems_extend. iIntros (empty) "Hempty".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_create. assumption. }
    iIntros (create) "#Hcreate".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (clear) "Hclear".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (add) "Hadd".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (push) "Hpush".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (peek) "Hpeek".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (peek_opt) "Hpeek_opt".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (top) "Htop".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (take) "Htake".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (take_opt) "Htake_opt".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (pop) "Hpop".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (copy) "Hcopy".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (is_empty) "His_empty".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (length) "Hlength".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (iter) "Hiter".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (fold) "Hfold".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (transfer) "Htransfer".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (to_seq) "Hto_seq".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (add_seq) "Hadd_seq".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (of_seq) "Hof_seq".

    iApply imp_sitems_nil.
    iFrame "#". simpl. auto.

Admitted.

End module_proof.
