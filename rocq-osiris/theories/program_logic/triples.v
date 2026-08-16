Require Import ewp.

(* [{{{] is a closed notation that also occurs in the middle of the notation,
   for which this warning is misleading. *)
Local Set Warnings "-closed-notation-not-level-0".

(** * Texan triples for the impure judgement [EWP].

  These are the analogue of Iris' Texan triples, adapted to Osiris' [impure]
  judgement. Recall that [EWP] has four parameters beyond the computation
  itself:

    EWP e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}

  - [E] : the mask (defaults to [⊤]),
  - [Ψ] : the effect protocol (defaults to [⊥], i.e. no effects allowed),
  - [ζ] : the exceptional postcondition (defaults to [⊥], i.e. no exception
          may escape),
  - [Φ] : the return postcondition.

  Both postconditions are put in continuation-passing ("Texan") form, so that
  each may be given as a pattern under its own binders: [RET] for the returning
  case and [EXN] for the exceptional one. The [EXN] clause may be omitted, in
  which case no exception may escape. The mask and the protocol are passed
  through verbatim and may be omitted, exactly as for [EWP]:

    {{{ P }}} e @ E <| Ψ |> {{{ x .. y, RET pat ; Q | u .. v, EXN epat ; S }}}

  Note that, unlike the [EWP] notation and like Iris' Texan triples, these are
  persistent: the triple may be used any number of times. *)

(** ** [RET] only, no binders *)

Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ EWP e {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ EWP e @ E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e <| Ψ '|>' {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ EWP e <| Ψ |> {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' <|  Ψ  |>  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e @ E <| Ψ '|>' {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ EWP e @ E <| Ψ |> {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  <|  Ψ  |>  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
    : bi_scope.

(** ** [RET] only, with binders *)

Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ EWP e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ EWP e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e <| Ψ '|>' {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ EWP e <| Ψ |> {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' <|  Ψ  |>  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e @ E <| Ψ '|>' {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ EWP e @ E <| Ψ |> {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  <|  Ψ  |>  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
    : bi_scope.

(** ** [RET] and [EXN], no binders *)

Notation "'{{{' P } } } e {{{ 'RET' pat ; Q '|' 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (Q -∗ Φ pat%V) -∗ ▷ (S -∗ Ξ epat%V) -∗ EWP e ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' RET  pat ;  '/' Q  '/' |  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q '|' 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (Q -∗ Φ pat%V) -∗ ▷ (S -∗ Ξ epat%V) -∗ EWP e @ E ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' {{{  '[' RET  pat ;  '/' Q  '/' |  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e <| Ψ '|>' {{{ 'RET' pat ; Q '|' 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (Q -∗ Φ pat%V) -∗ ▷ (S -∗ Ξ epat%V) -∗ EWP e <| Ψ |> ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' <|  Ψ  |>  '/' {{{  '[' RET  pat ;  '/' Q  '/' |  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e @ E <| Ψ '|>' {{{ 'RET' pat ; Q '|' 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (Q -∗ Φ pat%V) -∗ ▷ (S -∗ Ξ epat%V) -∗ EWP e @ E <| Ψ |> ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  <|  Ψ  |>  '/' {{{  '[' RET  pat ;  '/' Q  '/' |  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.

(** ** [RET] with binders, [EXN] without *)

Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q '|' 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ ▷ (S -∗ Ξ epat%V) -∗
      EWP e ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  '/' |  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q '|' 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ ▷ (S -∗ Ξ epat%V) -∗
      EWP e @ E ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  '/' |  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e <| Ψ '|>' {{{ x .. y , 'RET' pat ; Q '|' 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ ▷ (S -∗ Ξ epat%V) -∗
      EWP e <| Ψ |> ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' <|  Ψ  |>  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  '/' |  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e @ E <| Ψ '|>' {{{ x .. y , 'RET' pat ; Q '|' 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ ▷ (S -∗ Ξ epat%V) -∗
      EWP e @ E <| Ψ |> ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  <|  Ψ  |>  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  '/' |  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.

(** ** [RET] without binders, [EXN] with *)

Notation "'{{{' P } } } e {{{ 'RET' pat ; Q '|' u .. v , 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (Q -∗ Φ pat%V) -∗ ▷ (∀ u, .. (∀ v, S -∗ Ξ epat%V) .. ) -∗
      EWP e ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20, u closed binder, v closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' RET  pat ;  '/' Q  '/' |  u  ..  v ,  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q '|' u .. v , 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (Q -∗ Φ pat%V) -∗ ▷ (∀ u, .. (∀ v, S -∗ Ξ epat%V) .. ) -∗
      EWP e @ E ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20, u closed binder, v closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' {{{  '[' RET  pat ;  '/' Q  '/' |  u  ..  v ,  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e <| Ψ '|>' {{{ 'RET' pat ; Q '|' u .. v , 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (Q -∗ Φ pat%V) -∗ ▷ (∀ u, .. (∀ v, S -∗ Ξ epat%V) .. ) -∗
      EWP e <| Ψ |> ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20, u closed binder, v closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' <|  Ψ  |>  '/' {{{  '[' RET  pat ;  '/' Q  '/' |  u  ..  v ,  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e @ E <| Ψ '|>' {{{ 'RET' pat ; Q '|' u .. v , 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (Q -∗ Φ pat%V) -∗ ▷ (∀ u, .. (∀ v, S -∗ Ξ epat%V) .. ) -∗
      EWP e @ E <| Ψ |> ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20, u closed binder, v closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  <|  Ψ  |>  '/' {{{  '[' RET  pat ;  '/' Q  '/' |  u  ..  v ,  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.

(** ** [RET] and [EXN], both with binders *)

Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q '|' u .. v , 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. )
        -∗ ▷ (∀ u, .. (∀ v, S -∗ Ξ epat%V) .. ) -∗
      EWP e ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     u closed binder, v closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  '/' |  u  ..  v ,  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q '|' u .. v , 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. )
        -∗ ▷ (∀ u, .. (∀ v, S -∗ Ξ epat%V) .. ) -∗
      EWP e @ E ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     u closed binder, v closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  '/' |  u  ..  v ,  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e <| Ψ '|>' {{{ x .. y , 'RET' pat ; Q '|' u .. v , 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. )
        -∗ ▷ (∀ u, .. (∀ v, S -∗ Ξ epat%V) .. ) -∗
      EWP e <| Ψ |> ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     u closed binder, v closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' <|  Ψ  |>  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  '/' |  u  ..  v ,  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.

Notation "'{{{' P } } } e @ E <| Ψ '|>' {{{ x .. y , 'RET' pat ; Q '|' u .. v , 'EXN' epat ; S } } }" :=
  (□ ∀ Φ Ξ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. )
        -∗ ▷ (∀ u, .. (∀ v, S -∗ Ξ epat%V) .. ) -∗
      EWP e @ E <| Ψ |> ⟨⟨ Ξ ⟩⟩ {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     u closed binder, v closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' @  E  <|  Ψ  |>  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  '/' |  u  ..  v ,  EXN  epat ;  '/' S  ']' } } } ']'")
    : bi_scope.
