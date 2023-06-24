Definition call_encode `{Encode A} v (x : A) : free val :=
  call v #x.

Lemma call_encode_def `{Encode A} v1 v2 (x : A) :
  v2 = #x →
  call v1 v2 = call_encode v1 x.
Proof. intros. subst. reflexivity. Qed.

Ltac encode_calls :=
  repeat lazymatch goal with
    |- context[call ?v1 ?v2] =>
      erewrite ->(call_encode_def v1 v2) by solve [encode]
  end;
  unfold call_encode.
