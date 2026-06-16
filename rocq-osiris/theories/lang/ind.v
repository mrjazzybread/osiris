From osiris Require Import base.
Require Import syntax.


(* More complete induction schemes on syntax constructs, as needed *)

Section pat.

  Context
    (Ppat : pat → Prop)
    (Ppats : list pat → Prop)
    (Pfps : list (field * pat) → Prop)
  .

  Context
    (IH_PUnsupported : Ppat PUnsupported)
    (IH_PAny : Ppat PAny)
    (IH_PVar : ∀ v, Ppat (PVar v))
    (IH_PAlias : ∀ p v (IHp : Ppat p), Ppat (PAlias p v))
    (IH_POr : ∀ p1 p2 (IHp1 : Ppat p1) (IHp2 : Ppat p2), Ppat (POr p1 p2))
    (IH_PTuple : ∀ ps (IHps : Ppats ps), Ppat (PTuple ps))
    (IH_PData : ∀ d ps (IHps : Ppats ps), Ppat (PData d ps))
    (IH_PXData : ∀ π ps (IHps : Ppats ps), Ppat (PXData π ps))
    (IH_PRecord : ∀ fps (IHfps : Pfps fps), Ppat (PRecord fps))
    (IH_PArray : ∀ ps (IHps : Ppats ps), Ppat (PArray ps))
    (IH_PInt : ∀ z, Ppat (PInt z))
    (IH_PChar : ∀ c, Ppat (PChar c))
    (IH_PString : ∀ s, Ppat (PString s))
    (IH_pats_nil : Ppats [])
    (IH_pats_cons : ∀ p ps (IHp : Ppat p) (IHps : Ppats ps), Ppats (p :: ps))
    (IH_fps_nil : Pfps [])
    (IH_fps_cons : ∀ f p fps (IHp : Ppat p) (IHfps : Pfps fps), Pfps ((f, p) :: fps))
  .

  Fixpoint pat_ind p : Ppat p :=
    match p with
    | PUnsupported => IH_PUnsupported
    | PAny => IH_PAny
    | PVar v => IH_PVar v
    | PAlias p v => IH_PAlias p v (pat_ind p)
    | POr p1 p2 => IH_POr p1 p2 (pat_ind p1) (pat_ind p2)
    | PTuple ps =>
       let pats_ind := fix pats_ind ps : Ppats ps :=
           match ps with
           | [] => IH_pats_nil
           | p :: ps => IH_pats_cons p ps (pat_ind p) (pats_ind ps)
           end in
        IH_PTuple ps (pats_ind ps)
    | PData d ps =>
       let pats_ind := fix pats_ind ps : Ppats ps :=
           match ps with
           | [] => IH_pats_nil
           | p :: ps => IH_pats_cons p ps (pat_ind p) (pats_ind ps)
           end in
       IH_PData d ps (pats_ind ps)
    | PXData π ps =>
       let pats_ind := fix pats_ind ps : Ppats ps :=
           match ps with
           | [] => IH_pats_nil
           | p :: ps => IH_pats_cons p ps (pat_ind p) (pats_ind ps)
           end in
       IH_PXData π ps (pats_ind ps)
    | PRecord fps =>
       let fps_ind := fix fps_ind ps : Pfps ps :=
           match ps with
           | [] => IH_fps_nil
           | (f, p) :: ps => IH_fps_cons f p ps (pat_ind p) (fps_ind ps)
           end in
        IH_PRecord fps (fps_ind fps)
    | PArray ps =>
       let pats_ind := fix pats_ind ps : Ppats ps :=
           match ps with
           | [] => IH_pats_nil
           | p :: ps => IH_pats_cons p ps (pat_ind p) (pats_ind ps)
           end in
       IH_PArray ps (pats_ind ps)
    | PInt z => IH_PInt z
    | PChar c => IH_PChar c
    | PString s => IH_PString s
    end.

End pat.
