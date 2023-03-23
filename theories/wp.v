Require Import base lang free eval step safe.

Definition wp η e φ :=
  safe (eval η e) φ.
