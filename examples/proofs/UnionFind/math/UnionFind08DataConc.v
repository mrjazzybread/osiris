From osiris Require Import osiris.

Notation elem := record.

(* The static description of a content record; see below. The value
   carried by [CRoot] is the record's payload at allocation time — since a
   [Root] record's [value] field is never actually written again (see the
   comment above [content_own]), this value is permanent, and recording it
   in [cinfo] itself (rather than as a separate, ephemeral existential in
   [content_own]) is what lets [union]'s functional spec relate its
   returned [Some r] to a genuine, persistent fact (the discardable
   fragment [CtRoot rc ↪[γc]□ CRoot r]) instead of an unconstrained
   existential.

   [CLink] additionally records the *holder* [h]: the (unique) vertex
   whose content cell the link value was installed into. A link value is
   born in exactly one vertex's cell — [union]'s CAS — and is never
   moved to another (every CAS in the code swings a [Root] value out,
   never a [Link] in elsewhere), so the holder is as permanent as the
   bound and can live in the registration. It is what lets a reader of
   [x]'s content cell recognize, from the persistent fragment alone,
   that the link it loaded describes [x] itself — the key to [find]'s
   same-class postcondition. *)

Inductive cinfo :=
| CRoot (v : val)
| CLink (b : Z) (h : elem).

Instance inhabited_cinfo : Inhabited cinfo.
Proof. exact (populate (CLink 0%Z inhabitant)). Qed.

Section content.

  (* [content] is the *key* of the content registry [γc]: the registry
     maps each content value ever stored in a vertex's content cell to
     its static description [cinfo]. *)

  Inductive content :=
  | CtRoot (r : record)
  | CtLink (r : record).

  Definition content_loc (c : content) : record :=
    match c with CtRoot rc | CtLink rc => rc end.
  Definition content_root (c : content) : bool :=
    match c with CtRoot _ => true | CtLink _ => false end.
  Definition content_tag (c : content) :=
    match c with CtRoot _ => "Root" | CtLink _ => "Link" end.

  Global Instance content_eq_decision : EqDecision content.
  Proof. solve_decision. Defined.

  Global Instance content_countable : Countable content.
  Proof.
    apply (inj_countable' (λ c, (content_root c, content_loc c))
             (λ '(b, r), if b then CtRoot r else CtLink r)).
    by intros [].
  Defined.

  Global Instance content_inhabited : Inhabited content := populate (CtRoot (Loc 0%Z)).

  Global Instance Encode_content : Encode content :=
    {| encode' c := match c with
                    | CtRoot r => VInline "Root" r
                    | CtLink r => VInline "Link" r
                    end |}.
  Lemma content_encode_inline c :
    #c = VInline (content_tag c) (content_loc c).
  Proof. rewrite encode_encode'. by destruct c. Qed.

  Global Instance Inline_content_Root : Inline "Root" content :=
    {| inline_apply := CtRoot; inline_encode := λ _, eq_refl |}.

  Global Instance Inline_content_Link : Inline "Link" content :=
    {| inline_apply := CtLink; inline_encode := λ _, eq_refl |}.

End content.

(* The stored shape of a [content] value, for the rules (notably the
   CAS) that inspect the raw [VInline] representation. *)

(* ------------------------------------------------------------------------ *)
(* [RecordRepr] instances for the three record shapes allocated in this
   file ([Root{value}], [Link{parent}], the vertex's own {id;content}),
   so that [imp_record] can be used at their allocation sites instead of
   the raw tuple-level [imp_EInline]/[imp_ERecord]. *)

Record root_fields : Type := mkRootFields { root_value : val }.

Record link_fields : Type := mkLinkFields { link_parent : elem }.

Record vertex_fields : Type := mkVertexFields { vertex_id_f : Z; vertex_content_f : val }.

Instance root_fields_repr : RecordRepr root_fields τ[val] Mut :=
  { repr_to_types r := r.(root_value);
    types_to_repr := λ v, {| root_value := v |};
    repr_id := λ v, eq_refl }.

Instance link_fields_repr : RecordRepr link_fields τ[elem] Mut :=
  { repr_to_types r := r.(link_parent);
    types_to_repr := λ p, {| link_parent := p |};
    repr_id := λ p, eq_refl }.

Instance vertex_fields_repr : RecordRepr vertex_fields τ[Z; val] Mut :=
  { repr_to_types r := (r.(vertex_id_f), r.(vertex_content_f));
    types_to_repr := λ i c, {| vertex_id_f := i; vertex_content_f := c |};
    repr_id := λ '(i, c), eq_refl }.
