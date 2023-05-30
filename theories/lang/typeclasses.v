From osiris Require Import base.
From osiris.lang Require Import syntax.

Global Instance lookup_env : Lookup string val env :=
  fix go (name: string) (δ: env) : option val :=
    match δ with
    | EnvNil => None
    | EnvCons n v δ =>
        if n =? name
        then Some v
        else go name δ
    end.

Global Instance env_lookup_total : LookupTotal string val env :=
  fun (name: string) (η: env) =>
    match η !! name with
    | None => VUnit
    | Some v => v
    end.
