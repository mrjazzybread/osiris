(******************************************************************************)
(*                                                                            *)
(*                          The Herlihy-Wing queue                            *)
(*                                                                            *)
(******************************************************************************)

(* This module implements the concurrent queue of Herlihy and Wing (1990),
   the textbook example of a linearizable data structure whose operations
   have no fixed linearization point.

   The structure is an array of [capacity] one-shot slots together with a
   counter [back]. An enqueuer claims a slot by an atomic fetch-and-add on
   [back] and then fills it. A dequeuer reads [back], scans the slots below
   it from left to right, and takes the first one it finds filled; a slot is
   emptied and claimed in one step, by an atomic exchange.

   Every slot is therefore written at most twice: once by the enqueuer that
   claimed it, and once by the dequeuer that empties it. No slot is ever
   reused. *)

(* -------------------------------------------------------------------------- *)

(* A slot holds either nothing or one element. The field is [@atomic] so
   that filling a slot and emptying it are single steps that cannot be
   interleaved with one another. *)

type 'a slot = { mutable v : 'a option [@atomic] }

(* A queue is an array of slots plus the index [back] of the first slot that
   has not been claimed yet. [back] never decreases; slots are claimed in
   increasing order, one per [enqueue].

   [proph] is a ghost field: a single prophecy variable, created with the
   queue and resolved by every one of [scan]'s exchanges. It has no
   run-time meaning ([Proph.create ()] is a [unit ref], and the [@resolve]
   annotation is erased by the compiler), but it is what makes the FIFO
   specification provable. See the proof file: the order in which two
   concurrent enqueues linearize is not determined by the past, only by
   the sequence of elements the queue will hand out in the future.
   Resolving [proph] at every exchange makes that sequence readable. *)

type 'a t = {
  items : 'a slot array;
  proph : Proph.t;
  mutable back : int [@atomic];
}

(* -------------------------------------------------------------------------- *)

(* [create capacity] creates an empty queue that accepts [capacity] calls to
   [enqueue].

   Herlihy and Wing state the algorithm over an unbounded array. A real
   array is finite, so this implementation is a bounded queue: it is the
   caller's responsibility not to enqueue more than [capacity] times. Note
   that this is a bound on the total number of enqueues ever performed, not
   on the number of elements present at once, since slots are not reused. *)

let create (capacity : int) : 'a t =
  let items = Array.init capacity (fun _ -> { v = None }) in
  let proph = Proph.create () in
  { items; proph; back = 0 }

(* -------------------------------------------------------------------------- *)

(* [enqueue q x] adds [x] to the queue [q].

   The fetch-and-add hands this call a slot that no other call will ever
   receive, so the exchange that follows cannot race with another enqueuer.
   It may race with dequeuers, which is why it is atomic: a dequeuer sees
   the slot either empty or holding [x], never half-written.

   The exchange's result is discarded. It is necessarily [None]: the slot
   was claimed by this call and has not been filled since. *)

let enqueue (q : 'a t) (x : 'a) : unit =
  let i = Atomic.Loc.fetch_and_add [%atomic.loc q.back] 1 in
  let s = q.items.(i) in
  match Atomic.Loc.exchange [%atomic.loc s.v] (Some x) with
  | _ -> ()

(* -------------------------------------------------------------------------- *)

(* [scan q n i] looks for an element in the slots [i, n), left to right, and
   restarts from a freshly read bound when it reaches [n] without finding
   one. It does not return until it has taken an element, so it spins on an
   empty queue.

   Taking an element is a single exchange: the slot is read and emptied at
   once, so two dequeuers cannot take the same element. *)

let rec scan (q : 'a t) (n : int) (i : int) : 'a =
  if i >= n then
    (* This pass found nothing. Read [back] again, since it may have grown,
       and start over from the beginning of the array. *)
    let n = Atomic.Loc.get [%atomic.loc q.back] in
    scan q n 0
  else
    let s = q.items.(i) in
    let p = q.proph in
    match (Atomic.Loc.exchange [%atomic.loc s.v] None) [@resolve p i] with
    | Some x ->
        (* Slot [i] held [x], and now holds nothing. It is ours. *)
        x
    | None ->
        (* Slot [i] is either not filled yet or already emptied. Move on. *)
        scan q n (i + 1)
[@@warning "-26"] (* [p] is used only from the erased [@resolve] annotation *)

(* [dequeue q] removes and returns an element of [q]. *)

let dequeue (q : 'a t) : 'a =
  let n = Atomic.Loc.get [%atomic.loc q.back] in
  scan q n 0
