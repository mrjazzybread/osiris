From osiris Require Import osiris.

Require Export UnionFind00Update.

Notation elem := record.

(* ------------------------------------------------------------------------ *)
(* The ghost names of one union-find structure. *)

(* Five pieces of ghost state, bundled so that every predicate and every
   specification in the development takes ONE [γ]. They are:

   - [uf_vert]: [ghost_map elem Z], the vertices with their identifiers.
     Its fragments are persistent, and they are the membership tokens
     ([vertex], [in_uf]) every accessor uses to pull a vertex out of the
     invariant's big [∗ map].
   - [uf_link]: [ghost_map elem (option record)], a one-shot per vertex —
     [None] exclusively while the vertex is a root, [Some rc] persistently
     once it has been linked away ([linked]).
   - [uf_ids]: [ghost_map Z unit], one exclusive token per identifier in
     use, which is what makes identifiers injective ([id_tokens]).
   - [uf_class]: [auth (gset (elem * elem))], the pairs ever recorded as
     equivalent ([same_class]).
   - [uf_abs]: [ghost_var uf_state], the abstract state, of which the
     client holds one half ([UF]) and the invariant the other. *)

Record uf_names : Type := UfNames {
  uf_vert : gname;
  uf_link : gname;
  uf_ids : gname;
  uf_class : gname;
  uf_abs : gname;
}.

(* There used to be a [cinfo] here: a static description of each content
   record — the payload of a [Root], the bound and holder of a [Link] —
   kept in a registry mapping every content value ever installed to its
   description, so that a reader of a content cell could still say, much
   later, what the value it loaded was.

   Both halves of that are now had for less. A [Root] record's [value]
   field is never written after allocation (that is what its [mutable]
   annotation is for: forcing heap allocation, so that the physical
   equality test in [cas] is a pointer comparison), so the invariant
   hands out a *persistent* points-to for it and a reader needs no ghost
   state at all. A [Link] record is born in one vertex's cell and stays
   there forever — every CAS in the code swings a [Root] value out, never
   a [Link] — so the fact worth making permanent is about that vertex,
   not about the record: see [linked] in UnionFind10ReprPred.v. The bound
   went with it, being always the holder's own identifier. *)

Section content.

  (* [content] is the OCaml type ['a content]: the value a vertex's
     content cell holds, a tag together with a pointer to the record
     carrying that constructor's field. *)

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

  Global Instance InlineEncode_content : InlineEncode content :=
    {| inline_tag := content_tag;
       inline_blk := content_loc;
       inline_encode_eq := content_encode_inline |}.

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

Record vertex_fields : Type := mkVertexFields { vertex_id_f : Z; vertex_content_f : content }.

Instance root_fields_repr : RecordRepr root_fields τ[val] Mut :=
  { repr_to_types r := r.(root_value);
    types_to_repr := λ v, {| root_value := v |};
    repr_id := λ v, eq_refl }.

Instance link_fields_repr : RecordRepr link_fields τ[elem] Mut :=
  { repr_to_types r := r.(link_parent);
    types_to_repr := λ p, {| link_parent := p |};
    repr_id := λ p, eq_refl }.

Instance vertex_fields_repr : RecordRepr vertex_fields τ[Z; content] Mut :=
  { repr_to_types r := (r.(vertex_id_f), r.(vertex_content_f));
    types_to_repr := λ i c, {| vertex_id_f := i; vertex_content_f := c |};
    repr_id := λ '(i, c), eq_refl }.
