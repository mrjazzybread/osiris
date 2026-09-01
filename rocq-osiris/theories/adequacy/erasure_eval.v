From osiris.utils Require Import base list_z.
From osiris.lang Require Import lang ind.
From osiris.semantics Require Import semantics strategy.
Require Import erasure.

(* -------------------------------------------------------------------------- *)

(** * The erasure commutes with the interpreter. *)

(* [erase_eval] ties the erasure of computations to the erasure of
   syntax. Running the erasure of a program is running the erased
   program. *)

Fixpoint erase_fvals (fvs : list (field * val)) : list (field * val) :=
  match fvs with
  | [] => []
  | (f, v) :: fvs => (f, erase_val v) :: erase_fvals fvs
  end.

Definition erase_envs : envs → envs := prod_map erase_env erase_env.

(* -------------------------------------------------------------------------- *)

(** ** Value coercions. *)

(* Every [val_as_X] inspects the head constructor of a value and either
   returns a component of it or crashes. *)

Local Ltac erase_val_as v :=
  destruct v; simpl; repeat case_match;
    first [ apply EM_Crash | apply EM_Ret ].

Lemma erase_val_as_loc {E} (fE : E → E) v :
  erase_micro id fE (val_as_loc v) (val_as_loc (erase_val v)).
Proof. erase_val_as v. Qed.

Lemma erase_val_as_int (v : val) :
  erase_micro id erase_val (val_as_int v) (val_as_int (erase_val v)).
Proof. erase_val_as v. Qed.

Lemma erase_val_as_bool (v : val) :
  erase_micro id erase_val (val_as_bool v) (val_as_bool (erase_val v)).
Proof. erase_val_as v. Qed.

Lemma erase_val_as_thread {E} (fE : E → E) v :
  erase_micro id fE (val_as_thread v) (val_as_thread (erase_val v)).
Proof. erase_val_as v. Qed.

Lemma erase_val_as_cont {E} (fE : E → E) v :
  erase_micro id fE (val_as_cont v) (val_as_cont (erase_val v)).
Proof. erase_val_as v. Qed.

Lemma erase_val_as_struct {E} (fE : E → E) v :
  erase_micro erase_env fE (val_as_struct v) (val_as_struct (erase_val v)).
Proof. erase_val_as v. Qed.

(* -------------------------------------------------------------------------- *)

(** ** Environment lookups. *)

(* These are functions, not computations: erasure commutes with them as an
   equation. *)

Lemma erase_val_as_struct_opt v :
  val_as_struct_opt (erase_val v) = erase_env <$> val_as_struct_opt v.
Proof. by destruct v. Qed.

Lemma erase_lookup_name η x :
  lookup_name (erase_env η) x = erase_val <$> lookup_name η x.
Proof.
  induction η as [| [y v] η IH ]; simpl; first done.
  by case_match.
Qed.

Lemma erase_lookup_path η π :
  lookup_path (erase_env η) π = erase_val <$> lookup_path η π.
Proof.
  revert η. induction π as [| x π IH ]; intros η; simpl; first done.
  destruct π as [| y π ].
  - apply erase_lookup_name.
  - rewrite erase_lookup_name.
    destruct (lookup_name η x) as [ v | ]; simpl; last done.
    rewrite erase_val_as_struct_opt.
    destruct (val_as_struct_opt v) as [ xvs | ]; simpl; last done.
    apply IH.
Qed.

Lemma erase_eval_proph_arg η a :
  eval_proph_arg (erase_env η) a = erase_val <$> eval_proph_arg η a.
Proof. destruct a; simpl; [ apply erase_lookup_path | done | done ]. Qed.

(* -------------------------------------------------------------------------- *)

(** ** Coercions of computations. *)

Lemma erase_as_loc {E} (fE : E → E) m m' :
  erase_micro erase_val fE m m' → erase_micro id fE (as_loc m) (as_loc m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_loc.
Qed.

Lemma erase_as_int m m' :
  erase_micro erase_val erase_val m m' →
  erase_micro id erase_val (as_int m) (as_int m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_int.
Qed.

Lemma erase_as_bool m m' :
  erase_micro erase_val erase_val m m' →
  erase_micro id erase_val (as_bool m) (as_bool m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_bool.
Qed.

Lemma erase_as_thread {E} (fE : E → E) m m' :
  erase_micro erase_val fE m m' →
  erase_micro id fE (as_thread m) (as_thread m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_thread.
Qed.

Lemma erase_as_cont {E} (fE : E → E) m m' :
  erase_micro erase_val fE m m' → erase_micro id fE (as_cont m) (as_cont m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_cont.
Qed.

Lemma erase_as_struct {E} (fE : E → E) m m' :
  erase_micro erase_val fE m m' →
  erase_micro erase_env fE (as_struct m) (as_struct m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_struct.
Qed.

Lemma erase_val_as_record {E} (fE : E → E) v :
  erase_micro id fE (val_as_record v) (val_as_record (erase_val v)).
Proof. erase_val_as v. Qed.

Lemma erase_val_as_array {E} (fE : E → E) v :
  erase_micro id fE (val_as_array v) (val_as_array (erase_val v)).
Proof. erase_val_as v. Qed.

Lemma erase_as_record {E} (fE : E → E) m m' :
  erase_micro erase_val fE m m' → erase_micro id fE (as_record m) (as_record m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_record.
Qed.

Lemma erase_as_array {E} (fE : E → E) m m' :
  erase_micro erase_val fE m m' → erase_micro id fE (as_array m) (as_array m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_array.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Store operations. *)

Lemma erase_load {E} (fE : E → E) l :
  erase_micro erase_val fE (load l) (load l).
Proof.
  apply (EM_Stop _ _ CLoad); [ done | ].
  intros [ v | e ]; simpl; [ apply EM_Ret | apply EM_Crash ].
Qed.

Lemma erase_load_block {E} (fE : E → E) l :
  erase_micro id fE (load_block l) (load_block l).
Proof.
  apply (EM_Stop _ _ CLoadBlock); [ done | ].
  intros [ r | e ]; simpl; [ apply EM_Ret | apply EM_Crash ].
Qed.

Lemma erase_loadn {E} (fE : E → E) ls :
  erase_micro erase_vals fE (loadn ls) (loadn ls).
Proof.
  induction ls as [| l ls IH ]; simpl.
  - exact (EM_Ret erase_vals fE []).
  - eapply erase_bind; [ apply erase_load | ]. intros v.
    eapply erase_bind; [ apply IH | ]. intros vs.
    exact (EM_Ret erase_vals fE (v :: vs)).
Qed.

Lemma erase_alloc v :
  erase_micro id erase_val (alloc v) (alloc (erase_val v)).
Proof. apply (erase_stop CAlloc v). done. Qed.

Lemma erase_allocn vs :
  erase_micro id erase_val (allocn vs) (allocn (erase_vals vs)).
Proof.
  induction vs as [| v vs IH ]; simpl.
  - exact (EM_Ret id erase_val []).
  - eapply erase_bind; [ apply erase_alloc | ]. intros l.
    eapply erase_bind; [ apply IH | ]. intros ls.
    exact (EM_Ret id erase_val (l :: ls)).
Qed.

Lemma erase_alloc_block t ls :
  erase_micro id erase_val (alloc_block t ls) (alloc_block t ls).
Proof. apply (erase_stop CAllocBlock (t, ls)). done. Qed.

Lemma erase_exchange l v :
  erase_comp (exchange l v) (exchange l (erase_val v)).
Proof. apply (erase_stop CExchange (l, v)). done. Qed.

Lemma erase_store_op l v :
  erase_comp (code.store l v) (code.store l (erase_val v)).
Proof.
  unfold code.store.
  eapply erase_bind; [ apply erase_exchange | ]. intros w.
  exact (EM_Ret erase_val erase_val VUnit).
Qed.

Lemma erase_cas l seen v :
  erase_comp (cas l seen v) (cas l (erase_val seen) (erase_val v)).
Proof. apply (erase_stop CCAS (l, seen, v)). done. Qed.

Lemma erase_faa l i :
  erase_comp (faa l i) (faa l i).
Proof. apply (erase_stop CFAA (l, i)). done. Qed.

Lemma erase_set_tag l t :
  erase_micro id erase_val (set_tag l t) (set_tag l t).
Proof. apply (erase_stop CSetBlockTag (l, t)). done. Qed.

Lemma erase_update ls fvs :
  erase_micro id erase_val (update ls fvs) (update ls (erase_fvals fvs)).
Proof.
  induction fvs as [| [f v] fvs IH ]; simpl.
  - exact (EM_Ret id erase_val ()).
  - case_match; last apply EM_Crash.
    eapply erase_bind; [ apply erase_store_op | ]. intros w. apply IH.
Qed.

Lemma erase_loadfs {E} (fE : E → E) ls fps :
  erase_micro erase_vals fE (loadfs ls fps) (loadfs ls fps).
Proof.
  induction fps as [| [f p] fps IH ]; simpl.
  - exact (EM_Ret erase_vals fE []).
  - eapply erase_bind.
    { case_match; [ apply erase_load | apply EM_Crash ]. }
    intros v. eapply erase_bind; [ apply IH | ]. intros vs.
    exact (EM_Ret erase_vals fE (v :: vs)).
Qed.

(* [fvals] selects fields out of an already-loaded block; it is a function,
   not a computation. [!!!] returns the inhabitant of [val] on an index out
   of range, and that inhabitant is erasure-stable. *)

Lemma erase_val_inhabitant : erase_val inhabitant = inhabitant.
Proof. done. Qed.

(* -------------------------------------------------------------------------- *)

(** ** Arithmetic side conditions. *)

Lemma erase_check_div_by_zero i :
  erase_micro id erase_val (check_div_by_zero i) (check_div_by_zero i).
Proof.
  unfold check_div_by_zero. case_match.
  - apply EM_Crash.
  - exact (EM_Ret id erase_val ()).
Qed.

Lemma erase_if_in_shift_range {A E} (fA : A → A) (fE : E → E) i m m' :
  erase_micro fA fE m m' →
  erase_micro fA fE (if_in_shift_range i m) (if_in_shift_range i m').
Proof.
  intros Hm. unfold if_in_shift_range. case_match; [ done | apply EM_Crash ].
Qed.

(* [Array.make] builds its initial contents with [replicate]. *)

Lemma erase_vals_init_segment i k v :
  erase_vals (init_segment i k (λ _, v)) = init_segment i k (λ _, erase_val v).
Proof. revert i. induction k as [| k IH ]; intros i; simpl; by rewrite ?IH. Qed.

Lemma erase_vals_replicate n v :
  erase_vals (list_z.replicate n v) = list_z.replicate n (erase_val v).
Proof.
  unfold list_z.replicate, list_z.init. case_decide; first done.
  apply erase_vals_init_segment.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Comparisons. *)

(* The group where the erasure could have been unsound: [erase_expr] is not
   injective, so a comparison that looked inside a closure could equate
   values the annotated program distinguishes. Neither does — [phys_eq_val]
   accepts locations, blocks and constant constructors, [eq_val] integers,
   characters, strings, tuples and data, both error on the rest — so these
   hold with no side condition, where HeapLang needs [vals_compare_safe]. *)

Lemma erase_phys_eq_val v1 v2 :
  erase_micro id erase_val
    (phys_eq_val v1 v2) (phys_eq_val (erase_val v1) (erase_val v2)).
Proof.
  destruct v1, v2; simpl;
    try apply EM_Crash;
    (* Two blocks: both sides load the same two blocks and compare tags. *)
    try (eapply erase_bind;
         [ eapply erase_par; apply erase_load_block
         | intros [[t1 ls1] [t2 ls2]];
           cbn beta iota zeta delta [ id prod_map fst snd ];
           repeat case_match;
           first [ apply EM_Crash | exact (EM_Ret id erase_val _) ] ]);
    (* Constant constructors: the argument lists are erased pointwise, so
       one is empty exactly when the other is. *)
    try (destruct v as [| ? ? ], v0 as [| ? ? ]; simpl;
         first [ apply EM_Crash | exact (EM_Ret id erase_val _) ]);
    try (exact (EM_Ret id erase_val _)).
  (* A constant constructor against something that is not one: both sides
     take the error branch whatever the argument list looks like. *)
  all: solve [ repeat case_match; apply EM_Crash ].
Qed.

(* [eq_val] traverses tuples and data with a local [fix]; [eq_vals] mirrors
   it, so that the list case of the induction has something to be stated
   about. The two are convertible. *)

Fixpoint eq_vals (vs1 vs2 : list val) : micro bool exn :=
  match vs1, vs2 with
  | [], [] => ret true
  | v1 :: vs1, v2 :: vs2 =>
      b ← eq_val v1 v2 ;
      b' ← eq_vals vs1 vs2 ;
      ret (b && b')
  | _ :: _, [] | [], _ :: _ =>
      structural_equality_error "tuple length mismatch"
  end.

Lemma erase_eq_val v1 :
  ∀ v2, erase_micro id erase_val
          (eq_val v1 v2) (eq_val (erase_val v1) (erase_val v2)).
Proof.
  apply (val_ind
    (λ v1, ∀ v2, erase_micro id erase_val
                   (eq_val v1 v2) (eq_val (erase_val v1) (erase_val v2)))
    (λ vs1, ∀ vs2, erase_micro id erase_val
                     (eq_vals vs1 vs2) (eq_vals (erase_vals vs1)
                                                (erase_vals vs2))));
    intros; try (destruct v2; simpl; first [ apply EM_Crash
                                           | exact (EM_Ret id erase_val _) ]).
  - destruct v2; simpl; try apply EM_Crash. by apply IHvs.
  - destruct v2; simpl; try apply EM_Crash.
    case_match; last exact (EM_Ret id erase_val false). by apply IHvs.
  - destruct vs2; simpl; [ exact (EM_Ret id erase_val true) | apply EM_Crash ].
  - destruct vs2 as [| v2 vs2 ]; simpl; first apply EM_Crash.
    eapply erase_bind; [ apply IHv | ]. intros b.
    eapply erase_bind; [ apply IHvs | ]. intros b'.
    exact (EM_Ret id erase_val (b && b')).
Qed.

Lemma erase_ne_val v1 v2 :
  erase_micro id erase_val (ne_val v1 v2) (ne_val (erase_val v1) (erase_val v2)).
Proof.
  unfold ne_val. eapply erase_bind; [ apply erase_eq_val | ]. intros b.
  exact (EM_Ret id erase_val (negb b)).
Qed.

Lemma erase_lt_val v1 v2 :
  erase_micro id erase_val (lt_val v1 v2) (lt_val (erase_val v1) (erase_val v2)).
Proof.
  destruct v1, v2; simpl;
    first [ apply EM_Crash | exact (EM_Ret id erase_val _) ].
Qed.

Lemma erase_gt_val v1 v2 :
  erase_micro id erase_val (gt_val v1 v2) (gt_val (erase_val v1) (erase_val v2)).
Proof. apply erase_lt_val. Qed.

Lemma erase_le_val v1 v2 :
  erase_micro id erase_val (le_val v1 v2) (le_val (erase_val v1) (erase_val v2)).
Proof.
  unfold le_val. eapply erase_bind; [ apply erase_gt_val | ]. intros b.
  exact (EM_Ret id erase_val (negb b)).
Qed.

Lemma erase_ge_val v1 v2 :
  erase_micro id erase_val (ge_val v1 v2) (ge_val (erase_val v1) (erase_val v2)).
Proof.
  unfold ge_val. eapply erase_bind; [ apply erase_lt_val | ]. intros b.
  exact (EM_Ret id erase_val (negb b)).
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Effects and continuations. *)

Lemma erase_perform v : erase_comp (perform v) (perform (erase_val v)).
Proof. apply (erase_stop CPerf v). done. Qed.

Lemma erase_resume l o :
  erase_comp (resume l o) (resume l (erase_outcome o)).
Proof. apply (erase_stop CResume (l, o)). done. Qed.

Lemma erase_please_eval η e :
  erase_comp (please_eval η e) (please_eval (erase_env η) (erase_expr e)).
Proof. apply (erase_stop CEval (η, e)). done. Qed.

Lemma erase_wrap l η bs :
  erase_micro id erase_val
    (wrap l η bs) (wrap l (erase_env η) (erase_branches bs)).
Proof. apply (erase_stop CWrap (true, l, η, bs)). done. Qed.

Lemma erase_shallow_wrap l η bs :
  erase_micro id erase_val
    (shallow_wrap l η bs) (shallow_wrap l (erase_env η) (erase_branches bs)).
Proof. apply (erase_stop CWrap (false, l, η, bs)). done. Qed.

Lemma erase_wrap_outcome η bs (o : outcome3 val exn) :
  erase_micro erase_out3 erase_val
    (wrap_outcome η bs o)
    (wrap_outcome (erase_env η) (erase_branches bs) (erase_out3 o)).
Proof.
  destruct o as [ v | ex | ev k ]; simpl.
  - exact (EM_Ret erase_out3 erase_val (O3Ret v)).
  - exact (EM_Ret erase_out3 erase_val (O3Throw ex)).
  - eapply erase_bind; [ apply erase_wrap | ]. intros k'.
    exact (EM_Ret erase_out3 erase_val (O3Perform ev k')).
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Prophecies. *)

(* Allocating a prophecy and allocating a unit reference take the same step,
   so the two computations [eval] builds for them line up exactly. *)

Lemma erase_new_proph :
  erase_comp ('p ← new_proph ; ret (VLoc p)) ('l ← alloc VUnit ; ret (VLoc l)).
Proof.
  apply EM_NewProph. intros [ p | ex ]; simpl.
  - exact (EM_Ret erase_val erase_val (VLoc p)).
  - exact (EM_Throw erase_val erase_val ex).
Qed.

(* A resolution attached to a non-atomic expression compiles to a [CReturn]
   call on the value that expression produced. Erasure drops the call, so
   what is left is the erasure of the expression itself — whatever it does
   first. *)

Lemma erase_resolve_return w p v :
  erase_comp (resolve CReturn w p v) (ret (erase_val w)).
Proof. apply EM_ResolveReturn. apply EM_Ret. Qed.

Lemma erase_bind_resolve_return p v m m' :
  erase_comp m m' →
  erase_comp (bind m (λ w, resolve CReturn w p v)) m'.
Proof.
  intros Hm.
  (* The erased side does nothing after the expression; [bind m' ret] is [m']. *)
  rewrite <- (bind_ret_right m').
  eapply erase_bind; [ done | ]. intros w. apply erase_resolve_return.
Qed.

(* The four calls that may carry a fused resolution never throw: their steps
   return a value or crash. *)

Local Ltac no_throw :=
  intros σ σ' ex Hstep; destruct_step;
  unfold step_load_2, step_exchange_2, step_cas_2, step_faa_2 in *;
  repeat case_match; simplify_eq.

Lemma code_no_throw_load l : code_no_throw CLoad l.
Proof. no_throw. Qed.

Lemma code_no_throw_exchange x : code_no_throw CExchange x.
Proof. no_throw. Qed.

Lemma code_no_throw_cas x : code_no_throw CCAS x.
Proof. no_throw. Qed.

Lemma code_no_throw_faa x : code_no_throw CFAA x.
Proof. no_throw. Qed.

(* A resolution fused with an atomic operation erases to that operation.
   Exchange, compare-and-set and fetch-and-add even share a continuation;
   [load]'s differs, since its polymorphic error type forces it to crash on
   an exception it cannot carry — what [code_no_throw] excuses. *)

Lemma erase_resolve_load l p v :
  erase_comp (resolve CLoad l p v) (load l).
Proof.
  apply EM_Resolve; [ done | apply code_no_throw_load | ].
  intros w. apply EM_Ret.
Qed.

Lemma erase_resolve_exchange l w p v :
  erase_comp (resolve CExchange (l, w) p v) (exchange l (erase_val w)).
Proof.
  apply EM_Resolve; [ done | apply code_no_throw_exchange | ].
  intros u. apply EM_Ret.
Qed.

Lemma erase_resolve_cas l seen w p v :
  erase_comp (resolve CCAS (l, seen, w) p v)
             (cas l (erase_val seen) (erase_val w)).
Proof.
  apply EM_Resolve; [ done | apply code_no_throw_cas | ].
  intros u. apply EM_Ret.
Qed.

Lemma erase_resolve_faa l i p v :
  erase_comp (resolve CFAA (l, i) p v) (faa l i).
Proof.
  apply EM_Resolve; [ done | apply code_no_throw_faa | ].
  intros u. apply EM_Ret.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Threads, loops and choice. *)

Lemma erase_fork v1 v2 :
  erase_comp (fork v1 v2) (fork (erase_val v1) (erase_val v2)).
Proof. apply (erase_stop CFork (v1, v2)). done. Qed.

Lemma erase_join t : erase_comp (join t) (join t).
Proof. apply (erase_stop CJoin t). done. Qed.

Lemma erase_loop η x i1 i2 e :
  erase_comp (code.loop η x i1 i2 e)
             (code.loop (erase_env η) x i1 i2 (erase_expr e)).
Proof. apply (erase_stop CLoop (η, x, i1, i2, e)). done. Qed.

Lemma erase_flip : erase_micro id erase_val flip flip.
Proof. apply (erase_stop CFlip ()). done. Qed.

Lemma erase_choose {A} (fA : A → A) m1 m1' m2 m2' :
  erase_micro fA erase_val m1 m1' →
  erase_micro fA erase_val m2 m2' →
  erase_micro fA erase_val (choose m1 m2) (choose m1' m2').
Proof.
  intros Hm1 Hm2. unfold choose.
  eapply erase_bind; [ apply erase_flip | ]. intros b. by destruct b.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Calls. *)

(* A call does not evaluate the closure's body; it asks the machine to, with
   [stop CEval]. That keeps [eval] structurally recursive, and lets this be
   proved ahead of the induction: the body is an argument of a system call,
   erased by [erase_code_arg CEval]. *)

Lemma erase_env_app η1 η2 :
  erase_env (η1 ++ η2) = erase_env η1 ++ erase_env η2.
Proof. induction η1 as [| [x v] η1 IH ]; simpl; by rewrite ?IH. Qed.

Lemma erase_eval_rec_bindings_aux η rbs rbs' :
  eval_rec_bindings_aux (erase_env η) (erase_rec_bindings rbs)
                        (erase_rec_bindings rbs') =
  erase_env (eval_rec_bindings_aux η rbs rbs').
Proof. induction rbs' as [| [g a] rbs' IH ]; simpl; by rewrite ?IH. Qed.

Lemma erase_eval_rec_bindings η rbs :
  eval_rec_bindings (erase_env η) (erase_rec_bindings rbs) =
  erase_env (eval_rec_bindings η rbs).
Proof. apply erase_eval_rec_bindings_aux. Qed.

Lemma erase_lookup_rec_bindings rbs g :
  lookup_rec_bindings (erase_rec_bindings rbs) g =
  erase_anonfun <$> lookup_rec_bindings rbs g.
Proof.
  induction rbs as [| [g' a] rbs IH ]; simpl; first done. by case_match.
Qed.

Lemma erase_acall η a v :
  erase_comp (acall η a v) (acall (erase_env η) (erase_anonfun a) (erase_val v)).
Proof.
  destruct a as [ x e ]. unfold acall, please_eval.
  apply (erase_stop CEval ((x, v) :: η, e)). done.
Qed.

Lemma erase_call v1 v2 :
  erase_comp (call v1 v2) (call (erase_val v1) (erase_val v2)).
Proof.
  destruct v1; simpl; try apply EM_Crash.
  - apply erase_acall.
  - rewrite erase_eval_rec_bindings, erase_lookup_rec_bindings, <- erase_env_app.
    eapply erase_bind.
    + apply (erase_of_option erase_anonfun erase_val).
    + intros a. apply erase_acall.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Two-armed handlers. *)

Lemma erase_try {A B E E'} (fA : A → A) (fE' : E' → E') (fB : B → B) (fE : E → E)
    m m' (f : A → micro B E) f' (h : E' → micro B E) h' :
  erase_micro fA fE' m m' →
  (∀ a, erase_micro fB fE (f a) (f' (fA a))) →
  (∀ ex, erase_micro fB fE (h ex) (h' (fE' ex))) →
  erase_micro fB fE (try m f h) (try m' f' h').
Proof.
  intros Hm Hf Hh. unfold try.
  eapply erase_try2; [ done | ]. intros [ a | ex ]; simpl; [ apply Hf | apply Hh ].
Qed.

Lemma erase_orelse {A E E'} (fA : A → A) (fE' : E' → E') (fE : E → E)
    m1 m1' m2 m2' :
  erase_micro fA fE' m1 m1' →
  erase_micro fA fE m2 m2' →
  erase_micro fA fE (orelse m1 m2) (orelse m1' m2').
Proof.
  intros Hm1 Hm2. unfold orelse.
  eapply erase_try; [ done | intros a; apply EM_Ret | intros ex; done ].
Qed.

Lemma erase_vals_length vs : length (erase_vals vs) = length vs.
Proof.
  induction vs as [| v vs IH ]; first done.
  change (list_z.length (erase_val v :: erase_vals vs) =
          list_z.length (v :: vs)).
  rewrite !list_z.length_cons. by rewrite IH.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Module coercions and type extensions. *)

(* A coercion keeps a chosen set of a structure's fields and drops the rest.
   It inspects only field names, so it commutes with erasure — as an
   equation between options, since it is a function. [coerces] mirrors the
   local [fix] of [coerce], so that the list case has a statement. *)

Section Coerces.

(* The bind below is the option monad's, as in [pre_coerces]. *)
Local Open Scope stdpp.

Fixpoint coerces (xcs : list fcoercion) (xvs : env) : option env :=
  match xcs with
  | [] => Some []
  | (x, c) :: xcs =>
      v ← lookup_name xvs x ;
      v ← coerce c v ;
      xvs' ← coerces xcs xvs ;
      Some ((x, v) :: xvs')
  end.

End Coerces.

Lemma erase_coerce c :
  ∀ v, coerce c (erase_val v) = erase_val <$> coerce c v.
Proof.
  apply (coercion_ind
    (λ c, ∀ v, coerce c (erase_val v) = erase_val <$> coerce c v)
    (λ xcs, ∀ xvs, coerces xcs (erase_env xvs) = erase_env <$> coerces xcs xvs));
    (* [coerce]'s body carries the local [fix]; [coerces] is the same term *)
    intros; simpl; change (pre_coerces coerce) with coerces.
  - done.
  - rewrite erase_val_as_struct_opt.
    destruct (val_as_struct_opt v) as [ xvs | ]; simpl; last done.
    rewrite IHxcs. by destruct (coerces xcs xvs).
  - done.
  - rewrite erase_lookup_name.
    destruct (lookup_name xvs x) as [ v | ]; simpl; last done.
    rewrite IHc. destruct (coerce c0 v) as [ v' | ]; simpl; last done.
    rewrite IHxcs. by destruct (coerces xcs xvs).
Qed.

Lemma erase_eval_type_extensions cs :
  erase_micro erase_env erase_val
    (eval_type_extensions cs) (eval_type_extensions cs).
Proof.
  induction cs as [| c cs IH ]; simpl.
  - exact (EM_Ret erase_env erase_val []).
  - eapply erase_bind; [ apply (erase_alloc VUnit) | ]. intros l.
    eapply erase_bind; [ apply IH | ]. intros η.
    exact (EM_Ret erase_env erase_val ((c, VLoc l) :: η)).
Qed.


(* -------------------------------------------------------------------------- *)

(** ** Unfolding equations for the list evaluators. *)

(* [simpl_eval*] unseals and simplifies, which for a list evaluator goes one
   step too far: it inlines the head's evaluator too, and the induction
   hypothesis — stated with the sealed name — stops matching. These expose
   exactly one layer. They belong in eval.v next to [fold_pre_*]; they live
   here to avoid rebuilding the world. *)

Lemma evals_cons η e es :
  evals η (e :: es) =
  ('(v, vs) ← pair_op LiberalStrategy.tuple_order (eval η e) (evals η es) ;
   ret (v :: vs)).
Proof. unfold evals; rewrite seal_eq; by simpl. Qed.

Lemma evalfs_cons η f e fes :
  evalfs η (Fexpr f e :: fes) =
  ('(v, fvs) ← par (eval η e) (evalfs η fes) ; ret ((f, v) :: fvs)).
Proof. unfold evalfs; rewrite seal_eq; by simpl. Qed.

Lemma eval_bindings_cons η p e bs :
  eval_bindings η (Binding p e :: bs) =
  ('(v, δ) ← pair_op LiberalStrategy.let_and_order
               (eval η e) (eval_bindings η bs) ;
   irrefutably_extend η δ p v).
Proof. unfold eval_bindings; rewrite seal_eq; by simpl. Qed.

Lemma eval_sitems_cons ηδ i items :
  eval_sitems ηδ (i :: items) =
  (ηδ' ← eval_sitem ηδ i ; eval_sitems ηδ' items).
Proof.
  unfold eval_sitems, eval_sitem; rewrite !seal_eq; by simpl.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** The computation under a resolution. *)

(* [eval] reaches an expression by two doors: on its own, and under a
   resolution, where the four atomic operations compile to a fused [resolve]
   and everything else to a [CReturn]. This mirrors the second door so the
   induction can carry a statement about it — needed by the fused cases,
   which want the hypothesis for the operation's *argument*. Definitionally
   the body of [eval]'s [EResolve] clause. *)

Definition eval_resolved (η : env) (e : expr) (p : loc) (v : val) : microvx :=
  match e with
  | ELoad e1 =>
      l ← as_loc (eval η e1) ;
      resolve CLoad l p v
  | EExchange e1 e2 =>
      '(l, w) ← pair_op LiberalStrategy.fun_app_order
                  (as_loc (eval η e1)) (eval η e2) ;
      resolve CExchange (l, w) p v
  | ECAS e1 e2 e3 =>
      '(l, seen, w) ← par (par (as_loc (eval η e1)) (eval η e2)) (eval η e3) ;
      resolve CCAS (l, seen, w) p v
  | EFAA e1 e2 =>
      '(l, i) ← par (as_loc (eval η e1)) (as_int (eval η e2)) ;
      resolve CFAA (l, i) p v
  | _ =>
      w ← eval η e ;
      resolve CReturn w p v
  end.

Lemma erase_resolved_of_eval e :
  (∀ η p v, eval_resolved η e p v = (w ← eval η e ; resolve CReturn w p v)) →
  (∀ η, erase_comp (eval η e) (eval (erase_env η) (erase_expr e))) →
  ∀ η p v, erase_comp (eval_resolved η e p v)
             (eval (erase_env η) (erase_expr e)).
Proof.
  intros Hres He η p v. rewrite Hres. by apply erase_bind_resolve_return.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** The [erase_eval] lemma. *)

(* [ee_ret] threads the payload explicitly. *)

Local Ltac ee_ret :=
  lazymatch goal with
  | |- erase_micro ?fA ?fE (Ret ?a) _ => exact (EM_Ret fA fE a)
  | |- erase_micro ?fA ?fE (Throw ?e) _ => exact (EM_Throw fA fE e)
  end.

(* Fully destruct tuples. *)
Ltac destruct_pairs x :=
  repeat (let T := type of x in
          let T := eval hnf in T in
          lazymatch T with
          | (_ * _)%type => destruct x as [x ?]
          | unit => destruct x
          end).

(* After a [bind], the erased side has the payload map applied to the
   value that was just introduced. Reducing those makes the two sides
   line up again. *)
Local Ltac ee_pair :=
  cbn beta iota zeta delta [ id prod_map fst snd ].

(* A list evaluator applied to a cons. [ee_cons_eqs] exposes exactly one
   layer, keeping the head abstract and the evaluators sealed — which is how
   the induction hypotheses are stated. [ee_expose_cons] first reduces the
   erasure functions, since the erased side may still show the list as
   [erase_sitems (i :: items)] rather than as a cons. *)

Local Ltac ee_cons_eqs :=
  rewrite ?evals_cons, ?evalfs_cons, ?eval_bindings_cons, ?eval_sitems_cons.

Local Ltac ee_expose_cons :=
  cbn beta iota delta
    [ erase_exprs erase_fexprs erase_branches erase_bindings
      erase_rec_bindings erase_sitems ];
  ee_cons_eqs.

Lemma erase_eval_pat p :
  ∀ η δ v, erase_micro erase_env id
             (eval_pat η δ p v)
             (eval_pat (erase_env η) (erase_env δ) p (erase_val v)).
Proof.
  apply (pat_ind
    (λ p, ∀ η δ v, erase_micro erase_env id
                     (eval_pat η δ p v)
                     (eval_pat (erase_env η) (erase_env δ) p (erase_val v)))
    (λ ps, ∀ η δ vs, erase_micro erase_env id
                       (eval_pats η δ ps vs)
                       (eval_pats (erase_env η) (erase_env δ) ps
                                  (erase_vals vs)))
    (λ fps, ∀ η δ vs, erase_micro erase_env id
                        (eval_fpats η δ fps vs)
                        (eval_fpats (erase_env η) (erase_env δ) fps
                                    (erase_vals vs)))).
  (* A pattern holds no expressions, so both sides run the *same* pattern
     against a value and its erasure, and every test they make is one
     erasure preserves. The environment built is erased pointwise — the
     payload map here — and a failed match is a [throw ()] over [unit],
     unchanged. *)
  - (* PUnsupported *)
    intros η δ v; simpl_eval_pat; apply EM_Crash.
  - (* PAny *)
    intros η δ v; simpl_eval_pat; ee_ret.
  - (* PVar *)
    intros x η δ v; simpl_eval_pat; ee_ret.
  - (* PAlias *)
    intros q x IHq η δ v; simpl_eval_pat;
    eapply erase_bind; [ apply IHq | ]; intros δ'; ee_pair; ee_ret.
  - (* POr *)
    intros q1 q2 IHq1 IHq2 η δ v; simpl_eval_pat;
    eapply erase_orelse; [ apply IHq1 | apply IHq2 ].
  - (* PTuple *)
    intros ps IHps η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash; apply IHps.
  - (* PData *)
    intros d ps IHps η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash;
    case_match; [ apply IHps | ee_ret ].
  - (* PXData *)
    intros π ps IHps η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash;
    rewrite erase_lookup_path;
    eapply erase_bind; [ apply erase_as_loc, erase_of_option | ]; intros l';
    ee_pair;
    case_match; [ apply IHps | ee_ret ].
  - (* PRecord *)
    intros fps IHfps η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    eapply erase_bind; [ apply erase_loadfs | ]; intros vs; ee_pair;
    apply IHfps.
  - (* PInline *)
    intros d q IHq η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash;
    case_match; [ apply IHq | ee_ret ].
  - (* PArray *)
    intros ps IHps η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    eapply erase_bind; [ apply erase_loadn | ]; intros vs; ee_pair;
    rewrite erase_vals_length;
    case_decide; [ apply IHps | ee_ret ].
  - (* PInt *)
    intros z η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash;
    case_match; ee_ret.
  - (* PChar *)
    intros c η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash;
    case_match; ee_ret.
  - (* PString *)
    intros s η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash;
    case_match; ee_ret.
  - (* no pattern *)
    intros η δ vs;
    destruct vs; cbn beta iota delta [ erase_vals ]; simpl_eval_pats;
      [ ee_ret | apply EM_Crash ].
  - (* a pattern and the rest *)
    intros q ps IHq IHps η δ vs;
    destruct vs; cbn beta iota delta [ erase_vals ]; simpl_eval_pats;
      [ apply EM_Crash | ];
    eapply erase_bind; [ apply IHq | ]; intros δ'; ee_pair;
    eapply erase_bind; [ apply IHps | ]; intros δ''; ee_pair; ee_ret.
  - (* no field pattern *)
    intros η δ vs; simpl_eval_fpats; ee_ret.
  - (* a field pattern and the rest *)
    intros f q fps IHq IHfps η δ vs;
    destruct vs; cbn beta iota delta [ erase_vals ]; simpl_eval_fpats;
      [ apply EM_Crash | ];
    eapply erase_bind; [ apply IHq | ]; intros δ'; ee_pair;
    eapply erase_bind; [ apply IHfps | ]; intros δ''; ee_pair; ee_ret.
Qed.

Lemma erase_eval_cpat cp :
  ∀ η δ o, erase_micro erase_env id
             (eval_cpat η δ cp o)
             (eval_cpat (erase_env η) (erase_env δ) cp (erase_out3 o)).
Proof.
  induction cp as [ p | p | pe pk | cp1 IH1 cp2 IH2 ];
    intros η δ o; destruct o; simpl;
    first [ ee_ret
          | apply erase_eval_pat
          | eapply erase_bind;
              [ apply erase_eval_pat | intros δ'; apply erase_eval_pat ]
          (* [eapply]: the exception map of the first alternative appears
             only in that premise, so [apply] cannot infer it *)
          | eapply erase_orelse; [ apply IH1 | apply IH2 ] ].
Qed.

Lemma erase_irrefutably_extend {E} (fE : E → E) η δ p v :
  erase_micro erase_env fE
    (irrefutably_extend η δ p v)
    (irrefutably_extend (erase_env η) (erase_env δ) p (erase_val v)).
Proof.
  unfold irrefutably_extend.
  eapply erase_try; [ apply erase_eval_pat | intros δ'; apply EM_Ret | ].
  intros []. apply EM_Crash.
Qed.


Lemma erase_eval η e :
  erase_comp (eval η e) (eval (erase_env η) (erase_expr e)).
Proof.
  revert η.
  apply (expr_ind
    (* Pexpr: the expression on its own, and under a resolution. *)
    (λ e, (∀ η, erase_comp (eval η e) (eval (erase_env η) (erase_expr e)))
        ∧ (∀ η p v, erase_comp (eval_resolved η e p v)
                      (eval (erase_env η) (erase_expr e))))
    (* Pexprs *)
    (λ es, ∀ η, erase_micro erase_vals erase_val
                  (evals η es) (evals (erase_env η) (erase_exprs es)))
    (* Pfexpr *)
    (λ fe, match fe with
           | Fexpr _ e =>
               ∀ η, erase_comp (eval η e) (eval (erase_env η) (erase_expr e))
           end)
    (* Pfexprs *)
    (λ fes, ∀ η, erase_micro erase_fvals erase_val
                   (evalfs η fes) (evalfs (erase_env η) (erase_fexprs fes)))
    (* Pbranch *)
    (λ b, match b with
          | Branch _ e =>
              ∀ η, erase_comp (eval η e) (eval (erase_env η) (erase_expr e))
          end)
    (* Pbranches: the list as a deep handler, and as a shallow one. *)
    (λ bs, (∀ η o, erase_comp (eval_branches η o bs)
                     (eval_branches (erase_env η) (erase_out3 o)
                                    (erase_branches bs)))
         ∧ (∀ η all_bs o,
              erase_comp (shallow_eval_branches η bs all_bs o)
                (shallow_eval_branches (erase_env η) (erase_branches bs)
                                       (erase_branches all_bs)
                                       (erase_out3 o))))
    (* Pbinding *)
    (λ b, match b with
          | Binding _ e =>
              ∀ η, erase_comp (eval η e) (eval (erase_env η) (erase_expr e))
          end)
    (* Pbindings *)
    (λ bs, ∀ η, erase_micro erase_env erase_val
                  (eval_bindings η bs) (eval_bindings (erase_env η)
                                                      (erase_bindings bs)))
    (* Prec_binding *)
    (λ rb, match rb with
           | RecBinding _ (AnonFun _ e) =>
               ∀ η, erase_comp (eval η e) (eval (erase_env η) (erase_expr e))
           end)
    (* Prec_bindings *)
    (λ rbs, ∀ η, eval_rec_bindings (erase_env η) (erase_rec_bindings rbs) =
                 erase_env (eval_rec_bindings η rbs))
    (* Panonfun *)
    (λ a, match a with
          | AnonFun _ e =>
              ∀ η, erase_comp (eval η e) (eval (erase_env η) (erase_expr e))
          end)
    (* Pmexpr *)
    (λ me, ∀ η, erase_comp (eval_mexpr η me)
                  (eval_mexpr (erase_env η) (erase_mexpr me)))
    (* Psitem — stated with the two environments apart, so that [eval_sitem]
       can reduce; it matches on the pair. *)
    (λ i, ∀ η δ, erase_micro erase_envs erase_val
                   (eval_sitem (η, δ) i)
                   (eval_sitem (erase_env η, erase_env δ) (erase_sitem i)))
    (* Psitems *)
    (λ items, ∀ η δ, erase_micro erase_envs erase_val
                       (eval_sitems (η, δ) items)
                       (eval_sitems (erase_env η, erase_env δ)
                                    (erase_sitems items)))).
  (* One case per clause of [eval], each following the shape of the
     computation that clause builds. *)
  - (* EUnsupported *)
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval; apply EM_Crash.
  - (* EPath *)
    intros π;
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    rewrite erase_lookup_path; apply erase_of_option.
  - (* EAnonFun *)
    intros a IHa;
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval; ee_ret.
  - (* EApp *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe1 | apply IHe2 ] | ];
    intros [ v1 v2 ]; ee_pair; apply erase_call.
  - (* ETuple *)
    intros es IHes;
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply IHes | ]; intros vs; ee_pair; ee_ret.
  - (* EData *)
    intros c es IHes;
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply IHes | ]; intros vs; ee_pair; ee_ret.
  - (* EXData *)
    intros π es IHes;
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    rewrite erase_lookup_path;
    eapply erase_bind; [ apply erase_as_loc, erase_of_option | ]; intros l;
    ee_pair;
    eapply erase_bind; [ apply IHes | ]; intros vs; ee_pair; ee_ret.
  - (* ERecord *)
    intros t es IHes;
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply IHes | ]; intros vs; ee_pair;
    eapply erase_bind; [ apply erase_allocn | ]; intros ls; ee_pair;
    eapply erase_bind; [ apply erase_alloc_block | ]; intros l; ee_pair; ee_ret.
  - (* ERecordUpdate *)
    intros e0 fes [ IHe0 _ ] IHfes;
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par; [ apply erase_as_record, IHe0 | apply IHfes ] | ];
    intros [ r fvs ]; ee_pair;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    eapply erase_bind; [ apply erase_loadn | ]; intros vs; ee_pair;
    eapply erase_bind; [ apply erase_allocn | ]; intros ls'; ee_pair;
    eapply erase_bind; [ apply erase_update | ]; intros []; ee_pair;
    eapply erase_bind; [ apply erase_alloc_block | ]; intros l; ee_pair; ee_ret.
  - (* ERecordAccess *)
    intros e0 f [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_as_record, IHe0 | ]; intros r; ee_pair;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    destruct (ls !! f); [ apply erase_load | apply EM_Crash ].
  - (* ERecordSet *)
    intros e1 f e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par; [ apply erase_as_record, IHe1 | apply IHe2 ] | ];
    intros [ r v ]; ee_pair;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    destruct (ls !! f); [ apply erase_store_op | apply EM_Crash ].
  - (* EAtomicLoc *)
    intros e0 f [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_as_record, IHe0 | ]; intros r; ee_pair;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    destruct (ls !! f); [ ee_ret | apply EM_Crash ].
  - (* EInline *)
    intros c t es IHes;
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply IHes | ]; intros vs; ee_pair;
    eapply erase_bind; [ apply erase_allocn | ]; intros ls; ee_pair;
    eapply erase_bind; [ apply erase_alloc_block | ]; intros l; ee_pair; ee_ret.
  - (* EArrayLit *)
    intros es IHes;
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply IHes | ]; intros vs; ee_pair;
    eapply erase_bind; [ apply erase_allocn | ]; intros ls; ee_pair;
    eapply erase_bind; [ apply erase_alloc_block | ]; intros l; ee_pair; ee_ret.
  - (* EArrayLength *)
    intros e0 [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_as_array, IHe0 | ]; intros a; ee_pair;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    ee_ret.
  - (* EArrayGet *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_array, IHe1 | apply erase_as_int, IHe2 ] | ];
    intros [ a i ]; ee_pair;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    destruct (ls !! signed i); [ apply erase_load | apply EM_Crash ].
  - (* EArraySet *)
    intros e1 e2 e3 [ IHe1 _ ] [ IHe2 _ ] [ IHe3 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_array, IHe1 | apply erase_par;
              [ apply erase_as_int, IHe2 | apply IHe3 ] ] | ];
    intros [ a [ i v ] ]; ee_pair;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    destruct (ls !! signed i); [ apply erase_store_op | apply EM_Crash ].
  - (* EArrayMake *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par; [ apply erase_as_int, IHe1 | apply IHe2 ] | ];
    intros [ n v ]; ee_pair;
    case_decide; [ | apply EM_Crash ];
    rewrite <- erase_vals_replicate;
    eapply erase_bind; [ apply erase_allocn | ]; intros ls; ee_pair;
    eapply erase_bind; [ apply erase_alloc_block | ]; intros l; ee_pair; ee_ret.
  - (* EFreeze *)
    intros e0 [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_as_array, IHe0 | ]; intros a; ee_pair;
    eapply erase_bind; [ apply erase_set_tag | ]; intros []; ee_pair; ee_ret.
  - (* EUnfreeze *)
    intros e0 [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_as_array, IHe0 | ]; intros a; ee_pair;
    eapply erase_bind; [ apply erase_set_tag | ]; intros []; ee_pair; ee_ret.
  - (* EBoolConj *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_as_bool, IHe1 | ]; intros b; ee_pair;
    destruct b; [ apply IHe2 | ee_ret ].
  - (* EBoolDisj *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_as_bool, IHe1 | ]; intros b; ee_pair;
    destruct b; [ ee_ret | apply IHe2 ].
  - (* EBoolNeg *)
    intros e0 [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_as_bool, IHe0 | ]; intros b; ee_pair;
    ee_ret.
  - (* EInt *)
    intros i;
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval; ee_ret.
  - (* EMaxInt *)
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval; ee_ret.
  - (* EMinInt *)
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval; ee_ret.
  - (* EIntNeg *)
    intros e0 [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_as_int, IHe0 | ]; intros i; ee_pair;
    ee_ret.
  - (* EIntAdd *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe1 | apply erase_as_int, IHe2 ] | ];
    intros [ i1 i2 ]; ee_pair; ee_ret.
  - (* EIntSub *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe1 | apply erase_as_int, IHe2 ] | ];
    intros [ i1 i2 ]; ee_pair; ee_ret.
  - (* EIntMul *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe1 | apply erase_as_int, IHe2 ] | ];
    intros [ i1 i2 ]; ee_pair; ee_ret.
  - (* EIntDiv *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe1 | apply erase_as_int, IHe2 ] | ];
    intros [ i1 i2 ]; ee_pair;
    eapply erase_bind; [ apply erase_check_div_by_zero | ]; intros []; ee_pair;
    ee_ret.
  - (* EIntMod *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe1 | apply erase_as_int, IHe2 ] | ];
    intros [ i1 i2 ]; ee_pair;
    eapply erase_bind; [ apply erase_check_div_by_zero | ]; intros []; ee_pair;
    ee_ret.
  - (* EIntLand *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe1 | apply erase_as_int, IHe2 ] | ];
    intros [ i1 i2 ]; ee_pair; ee_ret.
  - (* EIntLor *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe1 | apply erase_as_int, IHe2 ] | ];
    intros [ i1 i2 ]; ee_pair; ee_ret.
  - (* EIntLxor *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe1 | apply erase_as_int, IHe2 ] | ];
    intros [ i1 i2 ]; ee_pair; ee_ret.
  - (* EIntLnot *)
    intros e0 [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_as_int, IHe0 | ]; intros i; ee_pair;
    ee_ret.
  - (* EIntLsl *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe1 | apply erase_as_int, IHe2 ] | ];
    intros [ i1 i2 ]; ee_pair; apply erase_if_in_shift_range; ee_ret.
  - (* EIntLsr *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe1 | apply erase_as_int, IHe2 ] | ];
    intros [ i1 i2 ]; ee_pair; apply erase_if_in_shift_range; ee_ret.
  - (* EIntAsr *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe1 | apply erase_as_int, IHe2 ] | ];
    intros [ i1 i2 ]; ee_pair; apply erase_if_in_shift_range; ee_ret.
  - (* EFloat *)
    intros f;
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval; ee_ret.
  - (* EChar *)
    intros c;
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval; ee_ret.
  - (* EString *)
    intros s;
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval; ee_ret.
  - (* EOpPhysEq *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe1 | apply IHe2 ] | ];
    intros [ v1 v2 ]; ee_pair;
    eapply erase_bind; [ apply erase_phys_eq_val | ]; intros b; ee_pair; ee_ret.
  - (* EOpEq *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe1 | apply IHe2 ] | ];
    intros [ v1 v2 ]; ee_pair;
    eapply erase_bind; [ apply erase_eq_val | ]; intros b; ee_pair; ee_ret.
  - (* EOpNe *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe1 | apply IHe2 ] | ];
    intros [ v1 v2 ]; ee_pair;
    eapply erase_bind; [ apply erase_ne_val | ]; intros b; ee_pair; ee_ret.
  - (* EOpLt *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe1 | apply IHe2 ] | ];
    intros [ v1 v2 ]; ee_pair;
    eapply erase_bind; [ apply erase_lt_val | ]; intros b; ee_pair; ee_ret.
  - (* EOpLe *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe1 | apply IHe2 ] | ];
    intros [ v1 v2 ]; ee_pair;
    eapply erase_bind; [ apply erase_le_val | ]; intros b; ee_pair; ee_ret.
  - (* EOpGt *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe1 | apply IHe2 ] | ];
    intros [ v1 v2 ]; ee_pair;
    eapply erase_bind; [ apply erase_gt_val | ]; intros b; ee_pair; ee_ret.
  - (* EOpGe *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe1 | apply IHe2 ] | ];
    intros [ v1 v2 ]; ee_pair;
    eapply erase_bind; [ apply erase_ge_val | ]; intros b; ee_pair; ee_ret.
  - (* ELet *)
    intros bs e0 IHbs [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply IHbs | ]; intros δ; ee_pair;
    rewrite <- erase_env_app; apply IHe0.
  - (* ELetRec *)
    intros rbs e0 IHrbs [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    rewrite IHrbs, <- erase_env_app; apply IHe0.
  - (* ELetModule *)
    intros M me e0 IHme [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply IHme | ]; intros v; ee_pair; apply IHe0.
  - (* ELetOpen *)
    intros me e0 IHme [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_as_struct, IHme | ]; intros δ; ee_pair;
    rewrite <- erase_env_app; apply IHe0.
  - (* ESeq *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply IHe1 | ]; intros w; ee_pair; apply IHe2.
  - (* EIfThen *)
    intros e0 e1 [ IHe0 _ ] [ IHe1 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_as_bool, IHe0 | ]; intros b; ee_pair;
    destruct b; [ apply IHe1 | ee_ret ].
  - (* EIfThenElse *)
    intros e0 e1 e2 [ IHe0 _ ] [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_as_bool, IHe0 | ]; intros b; ee_pair;
    destruct b; [ apply IHe1 | apply IHe2 ].
  - (* EMatch *)
    intros e0 bs [ IHe0 _ ] [ IHbs _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    apply EM_Handle; [ apply IHe0 | ]; intros o; simpl_wrap_eval_branches;
    eapply erase_bind; [ apply erase_wrap_outcome | ]; intros o'; ee_pair;
    apply IHbs.
  - (* EShallowMatch *)
    intros e0 bs [ IHe0 _ ] [ _ IHbs ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    apply EM_Handle; [ apply IHe0 | ]; intros o; apply IHbs.
  - (* ERaise *)
    intros e0 [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply IHe0 | ]; intros w; ee_pair; ee_ret.
  - (* EPerform *)
    intros e0 [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply IHe0 | ]; intros w; ee_pair; apply erase_perform.
  - (* EContinue *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par; [ apply erase_as_cont, IHe1 | apply IHe2 ] | ];
    intros [ l w ]; ee_pair; apply erase_resume.
  - (* EDiscontinue *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par; [ apply erase_as_cont, IHe1 | apply IHe2 ] | ];
    intros [ l w ]; ee_pair; apply erase_resume.
  - (* EWhile *)
    intros e0 body [ IHe0 _ ] [ IHbody _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_as_bool, IHe0 | ]; intros b; ee_pair;
    destruct b; [ | ee_ret ];
    eapply erase_bind; [ apply IHbody | ]; intros w; ee_pair;
    apply erase_please_eval.
  - (* EFor *)
    intros x e1 e2 e0 [ IHe1 _ ] [ IHe2 _ ] [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe1 | apply erase_as_int, IHe2 ] | ];
    intros [ i1 i2 ]; ee_pair; apply erase_loop.
  - (* EAssertFalse *)
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval; apply EM_Crash.
  - (* EAssert *)
    intros e0 [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    apply erase_choose; [ ee_ret | ];
    eapply erase_bind; [ apply erase_as_bool, IHe0 | ]; intros b; ee_pair;
    destruct b; [ ee_ret | apply EM_Crash ].
  - (* ERef *)
    intros e0 [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply IHe0 | ]; intros w; ee_pair;
    eapply erase_bind; [ apply erase_alloc | ]; intros l; ee_pair; ee_ret.
  - (* ELoad *)
    intros e0 [ IHe0 _ ]. split.
    + intros η. simpl_eval.
      eapply erase_bind; [ apply erase_as_loc, IHe0 | ]. intros l. ee_pair.
      apply erase_load.
    + intros η p v. cbn beta iota delta [ eval_resolved ]. simpl_eval.
      eapply erase_bind; [ apply erase_as_loc, IHe0 | ]. intros l. ee_pair.
      apply erase_resolve_load.
  - (* EStore *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par; [ apply erase_as_loc, IHe1 | apply IHe2 ] | ];
    intros [ l w ]; ee_pair; apply erase_store_op.
  - (* EExchange *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ]. split.
    + intros η. simpl_eval.
      eapply erase_bind;
        [ apply erase_par; [ apply erase_as_loc, IHe1 | apply IHe2 ] | ].
      intros [ l w ]. ee_pair. apply erase_exchange.
    + intros η p v. cbn beta iota delta [ eval_resolved ]. simpl_eval.
      eapply erase_bind;
        [ apply erase_pair_op; [ apply erase_as_loc, IHe1 | apply IHe2 ] | ].
      intros [ l w ]. ee_pair. apply erase_resolve_exchange.
  - (* ECAS *)
    intros e1 e2 e3 [ IHe1 _ ] [ IHe2 _ ] [ IHe3 _ ]. split.
    + intros η. simpl_eval.
      eapply erase_bind;
        [ apply erase_par;
            [ apply erase_par; [ apply erase_as_loc, IHe1 | apply IHe2 ]
            | apply IHe3 ] | ].
      intros [ [ l seen ] w ]. ee_pair. apply erase_cas.
    + intros η p v. cbn beta iota delta [ eval_resolved ]. simpl_eval.
      eapply erase_bind;
        [ apply erase_par;
            [ apply erase_par; [ apply erase_as_loc, IHe1 | apply IHe2 ]
            | apply IHe3 ] | ].
      intros [ [ l seen ] w ]. ee_pair. apply erase_resolve_cas.
  - (* EFAA *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ]. split.
    + intros η. simpl_eval.
      eapply erase_bind;
        [ apply erase_par;
            [ apply erase_as_loc, IHe1 | apply erase_as_int, IHe2 ] | ].
      intros [ l i ]. ee_pair. apply erase_faa.
    + intros η p v. cbn beta iota delta [ eval_resolved ]. simpl_eval.
      eapply erase_bind;
        [ apply erase_par;
            [ apply erase_as_loc, IHe1 | apply erase_as_int, IHe2 ] | ].
      intros [ l i ]. ee_pair. apply erase_resolve_faa.
  - (* ENewProph *)
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval; apply erase_new_proph.
  - (* EResolve *)
    intros e0 π a [ _ IHres ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    destruct (lookup_path η π) as [ [ ] | ]; try unfold as_loc; simpl;
    try apply EM_CrashL;
    destruct (eval_proph_arg η a) as [ w | ]; simpl; try apply EM_CrashL;
    apply IHres.
  - (* EIgnore *)
    intros e0 [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply IHe0 | ]; intros w; ee_pair; ee_ret.
  - (* EFork *)
    intros e1 e2 [ IHe1 _ ] [ IHe2 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe1 | apply IHe2 ] | ];
    intros [ f w ]; ee_pair; apply erase_fork.
  - (* EJoin *)
    intros e0 [ IHe0 _ ];
    apply and_dup; [ apply erase_resolved_of_eval; done | ]; intros η;
    simpl_eval;
    eapply erase_bind; [ apply erase_as_thread, IHe0 | ]; intros t; ee_pair;
    apply erase_join.
  - (* Fexpr *)
    intros f e0 [ IHe0 _ ]; exact IHe0.
  - (* Branch *)
    intros cp e0 [ IHe0 _ ]; exact IHe0.
  - (* Binding *)
    intros p e0 [ IHe0 _ ]; exact IHe0.
  - (* RecBinding *)
    intros f a IHa; exact IHa.
  - (* AnonFun *)
    intros x e0 [ IHe0 _ ]; exact IHe0.
  - (* MUnsupported *)
    intros η; simpl_eval_mexpr; apply EM_Crash.
  - (* MPath *)
    intros π η; simpl_eval_mexpr;
    rewrite erase_lookup_path; apply erase_of_option.
  - (* MStruct *)
    intros items IHitems η; simpl_eval_mexpr;
    eapply erase_bind; [ apply (IHitems η []) | ]; intros [ η' δ ]; ee_pair;
    ee_ret.
  - (* MFunctor *)
    intros x items IHitems η; simpl_eval_mexpr; ee_ret.
  - (* MCoercion *)
    intros me c IHme η; simpl_eval_mexpr;
    eapply erase_bind; [ apply IHme | ]; intros v; ee_pair;
    rewrite erase_coerce; apply erase_of_option.
  - (* ILet *)
    intros bs IHbs η δ; simpl_eval_sitem;
    eapply erase_bind; [ apply IHbs | ]; intros δ'; ee_pair;
    rewrite <- !erase_env_app; ee_ret.
  - (* ILetRec *)
    intros rbs IHrbs η δ; simpl_eval_sitem;
    rewrite IHrbs, <- !erase_env_app; ee_ret.
  - (* IModule *)
    intros m me IHme η δ; simpl_eval_sitem;
    eapply erase_bind; [ apply IHme | ]; intros v; ee_pair; ee_ret.
  - (* IOpen *)
    intros me IHme η δ; simpl_eval_sitem;
    eapply erase_bind; [ apply erase_as_struct, IHme | ]; intros δ'; ee_pair;
    rewrite <- erase_env_app; ee_ret.
  - (* IInclude *)
    intros me IHme η δ; simpl_eval_sitem;
    eapply erase_bind; [ apply erase_as_struct, IHme | ]; intros δ'; ee_pair;
    rewrite <- !erase_env_app; ee_ret.
  - (* IExternal *)
    intros x e0 [ IHe0 _ ] η δ; simpl_eval_sitem;
    eapply erase_bind; [ apply (IHe0 []) | ]; intros v; ee_pair; ee_ret.
  - (* IExtend *)
    intros cs η δ; simpl_eval_sitem;
    eapply erase_bind; [ apply erase_eval_type_extensions | ]; intros δ';
    ee_pair;
    rewrite <- !erase_env_app; ee_ret.
  - (* no expression *)
    intros η; ee_expose_cons; simpl_evals; ee_ret.
  - (* an expression and the rest *)
    intros e0 es [ IHe0 _ ] IHes η; ee_expose_cons;
    eapply erase_bind; [ apply erase_pair_op; [ apply IHe0 | apply IHes ] | ];
    intros [ v vs ]; ee_pair; ee_ret.
  - (* no field *)
    intros η; ee_expose_cons; simpl_evalfs; ee_ret.
  - (* a field and the rest *)
    intros [ f e0 ] fes IHfe IHfes η; ee_expose_cons;
    eapply erase_bind; [ apply erase_par; [ apply IHfe | apply IHfes ] | ];
    intros [ v fvs ]; ee_pair; ee_ret.
  - (* no branch: the outcome is propagated *)
    split.
    + intros η o. ee_expose_cons. unfold eval_branches; rewrite seal_eq.
      destruct o; cbn beta iota delta [ pre_eval_branches erase_out3 ].
      * apply EM_Crash.
      * ee_ret.
      * eapply erase_try2; [ apply erase_perform | ]. intros o'.
        apply erase_resume.
    + intros η all_bs o. ee_expose_cons.
      unfold shallow_eval_branches; rewrite seal_eq.
      destruct o; cbn beta iota delta [ pre_shallow_eval_branches erase_out3 ].
      * apply EM_Crash.
      * ee_ret.
      * eapply erase_bind; [ apply erase_shallow_wrap | ]. intros l. ee_pair.
        eapply erase_try2; [ apply erase_perform | ]. intros o'.
        apply erase_resume.
  - (* a branch and the rest *)
    intros [ cp e0 ] bs IHb [ IHbs IHsbs ]. split.
    + intros η o. ee_expose_cons. unfold eval_branches; rewrite seal_eq.
      cbn beta iota delta [ pre_eval_branches ].
      rewrite ?fold_pre_eval_branches.
      eapply erase_try2; [ apply erase_eval_cpat | ].
      intros [ δ | [] ]; cbn beta iota delta [ erase_out2 ].
      * apply IHb.
      * apply IHbs.
    + intros η all_bs o. ee_expose_cons.
      unfold shallow_eval_branches; rewrite seal_eq.
      cbn beta iota delta [ pre_shallow_eval_branches ].
      rewrite ?fold_pre_shallow_eval_branches.
      eapply erase_try.
      * apply erase_eval_cpat.
      * intros δ. apply IHb.
      * intros []. apply IHsbs.
  - (* no binding *)
    intros η; ee_expose_cons; simpl_eval_bindings; ee_ret.
  - (* a binding and the rest *)
    intros [ p e0 ] bs IHb IHbs η; ee_expose_cons;
    eapply erase_bind; [ apply erase_pair_op; [ apply IHb | apply IHbs ] | ];
    intros [ v δ ]; ee_pair; apply erase_irrefutably_extend.
  - (* no recursive binding *)
    intros η; apply erase_eval_rec_bindings.
  - (* a recursive binding and the rest *)
    intros rb rbs IHrb IHrbs η; apply erase_eval_rec_bindings.
  - (* no structure item *)
    intros η δ; ee_expose_cons; simpl_eval_sitems; ee_ret.
  - (* a structure item and the rest *)
    intros i items IHi IHitems η δ; ee_expose_cons;
    eapply erase_bind; [ apply IHi | ]; intros [ η' δ' ]; ee_pair;
    apply IHitems.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Branch lists on their own. *)

(* The metatheory also meets a branch list with no expression in scope:
   [StepWrap] stores a continuation re-installing a handler, whose branches
   are the [CWrap] argument. [branches_ind] would mean re-proving all of
   [expr_ind]'s premises; the bodies only need [erase_eval], so a plain
   induction on the list does. *)

Lemma erase_eval_branches bs :
  ∀ η o, erase_comp (eval_branches η o bs)
           (eval_branches (erase_env η) (erase_out3 o) (erase_branches bs)).
Proof.
  induction bs as [| [ cp e0 ] bs IH ]; intros η o.
  - (* no branch left: the outcome is propagated *)
    unfold eval_branches; rewrite seal_eq.
    destruct o;
      cbn beta iota delta [ pre_eval_branches erase_out3 erase_branches ].
    + apply EM_Crash.
    + ee_ret.
    + eapply erase_try2; [ apply erase_perform | ]. intros o'.
      apply erase_resume.
  - (* a branch: its body on a match, the remaining branches otherwise *)
    cbn beta iota delta [ erase_branches ].
    unfold eval_branches; rewrite seal_eq.
    cbn beta iota delta [ pre_eval_branches ].
    rewrite ?fold_pre_eval_branches.
    eapply erase_try2; [ apply erase_eval_cpat | ].
    intros [ δ | [] ]; cbn beta iota delta [ erase_out2 ].
    + apply erase_eval.
    + apply IH.
Qed.

Lemma erase_shallow_eval_branches bs :
  ∀ η all_bs o,
    erase_comp (shallow_eval_branches η bs all_bs o)
      (shallow_eval_branches (erase_env η) (erase_branches bs)
                             (erase_branches all_bs) (erase_out3 o)).
Proof.
  induction bs as [| [ cp e0 ] bs IH ]; intros η all_bs o.
  - (* no branch left: an unhandled effect reinstalls the handler *)
    unfold shallow_eval_branches; rewrite seal_eq.
    destruct o;
      cbn beta iota delta
        [ pre_shallow_eval_branches erase_out3 erase_branches ].
    + apply EM_Crash.
    + ee_ret.
    + eapply erase_bind; [ apply erase_shallow_wrap | ]. intros l. ee_pair.
      eapply erase_try2; [ apply erase_perform | ]. intros o'.
      apply erase_resume.
  - (* a branch: its body on a match, the remaining branches otherwise *)
    cbn beta iota delta [ erase_branches ].
    unfold shallow_eval_branches; rewrite seal_eq.
    cbn beta iota delta [ pre_shallow_eval_branches ].
    rewrite ?fold_pre_shallow_eval_branches.
    eapply erase_try.
    + apply erase_eval_cpat.
    + intros δ. apply erase_eval.
    + intros []. apply IH.
Qed.



Lemma erase_wrap_eval_branches η bs o :
  erase_comp (wrap_eval_branches η bs o)
    (wrap_eval_branches (erase_env η) (erase_branches bs) (erase_out3 o)).
Proof.
  simpl_wrap_eval_branches.
  eapply erase_bind; [ apply erase_wrap_outcome | ]. intros o'. ee_pair.
  apply erase_eval_branches.
Qed.


(* [StepLoop] replaces the [CLoop] call by the loop's own definition, so the
   metatheory needs the erasure of that too, not only of the call —
   [erase_loop] above relates the calls. *)

Lemma erase_loop_body η x i1 i2 e :
  erase_comp (E.loop η x i1 i2 e) (E.loop (erase_env η) x i1 i2 (erase_expr e)).
Proof.
  unfold E.loop. case_match.
  - (* the last iteration: run the body and stop *)
    eapply erase_bind; [ apply erase_eval | ]. intros w. ee_pair. ee_ret.
  - case_match.
    + (* the bounds cross: nothing to do *)
      ee_ret.
    + (* run the body, then ask for the next iteration *)
      eapply erase_bind; [ apply erase_eval | ]. intros w. ee_pair.
      apply erase_loop.
Qed.
