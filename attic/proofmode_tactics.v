
(* -------------------------------------------------------------------------- *)

(* Auxiliary definitions *)

Fixpoint environment_support η : list string :=
  match η with
  | EnvNil => []
  | EnvCons s _ η => s :: environment_support η
  end.

Definition spec_support `{!osirisGS_gen hlc Σ} : list (string * (val → iProp Σ)) → list string :=
  List.map fst.

Fixpoint in_bool' (s : string) (l : list string) : bool * list string :=
  match l with
  | [] => (false, [])
  | h :: l =>
      if (s =? h)%string
      then (true, l)
      else match in_bool' s l with
           | (true, l) => (true, h :: l)
           | (false, _) => (false, h :: l)
           end
  end.

Fixpoint in_bool (s : string) (l : list string) : bool :=
  match l with
  | [] => false
  | h :: l =>
      if (s =? h)%string
      then true
      else in_bool s l
  end.

Global Instance string_list_intersection : Intersection (list string) :=
  fix go l l' :=
    match l with
    | [] => []
    | h :: l =>
        match in_bool' h l' with
        | (false, l') => go l l'
        | (true, l') => h :: go l l'
        end
    end.

Global Instance string_list_difference : Difference (list string) :=
  fix go l l' :=
    match l with
    | [] => []
    | h :: l =>
        match in_bool h l' with
        | false => h :: go l l'
        | true => go l l'
        end
    end.

Definition has_specs `{!osirisGS_gen hlc Σ} (η: env) (Λ: list (string * (val → iProp Σ))) :=
  match intersection (environment_support η)
                     (spec_support Λ) with
  | [] => false
  | _ => true
  end.

Fixpoint from_pattern (p: pat) : list string :=
  match p with
  | PAny => []
  | PVar v => [v]
  | PAlias p v => v :: from_pattern p
  | PTuple ps => from_patterns ps
  | POr p1 p2 => (* Over approximation. *)
      from_pattern p1 ++ from_pattern p2
  | PData _ p => from_pattern p
  | PRecord fps => from_fpatterns fps
  | _ => [] (* Constants. *)
  end
with from_fpatterns fps :=
       match fps with
       | FPNil => []
       | FPCons _ p fps => from_pattern p ++ from_fpatterns fps
       end
with from_patterns (ps: pats) : list string :=
       match ps with
       | PNil => []
       | PCons p ps => from_pattern p ++ from_patterns ps
       end.

Definition module_defines (m: mexpr) : list string :=
  let from_bindings : bindings → list string :=
    fix go bds :=
      match bds with
      | BiNil => []
      | BiCons (Binding p _) bds =>
          from_pattern p ++ go bds
      end
  in
  let from_rec_bindings : rec_bindings → list string :=
    fix go bds :=
      match bds with
      | RecBiNil => []
      | RecBiCons (RecBinding v _) bds =>
          v :: go bds
      end
  in
  let from_item : sitem → list string :=
    fun item =>
      match item with
      | ILet bds => from_bindings bds
      | ILetRec bds => from_rec_bindings bds
      | _ => [] (* TODO. *)
      end
  in
  let from_items : sitems → list string :=
    fix go items :=
      match items with
      | INil => []
      | ICons item items =>
          from_item item ++ go items
      end
  in
  match m with
  | MStruct items => from_items items
  | _ => [] (* TODO. *)
  end.

Definition id_spec {A} (a: A) := a.
Global Opaque id_spec.

Definition id_continue {A} (a: A) := a.
Global Opaque id_continue.

