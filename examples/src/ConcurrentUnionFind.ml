(******************************************************************************)
(*                                                                            *)
(*                                 UnionFind                                  *)
(*                                                                            *)
(*                       François Pottier, Inria Paris                        *)
(*                                                                            *)
(*  Copyright Inria. All rights reserved. This file is distributed under      *)
(*  the terms of the GNU Library General Public License version 2, with a     *)
(*  special exception on linking, as described in the file LICENSE.           *)
(*                                                                            *)
(******************************************************************************)

(* This module offers a concurrent variant of the union-find data structure.

   The data structure is based on disjoint set forests. Path compression is
   performed as usual, using ordinary write instructions (as opposed to CAS
   instructions) because data races during path compression are benign.

   Linking is by random index. Every vertex carries a unique identifier whose
   most significant bits are randomly generated. When two vertices are linked,
   a comparison between their identifiers determines the direction of the new
   link: we maintain the invariant property that the parent always has a
   smaller identifier than the child. This ensures that, even in concurrent
   scenarios, no cycle can appear. *)

let cas = Atomic.Loc.compare_and_set

(* -------------------------------------------------------------------------- *)

(* The content of a vertex is either
   - a pointer to a parent vertex, or
   - a user value. *)

(* Path compression updates the [parent] field of the [Link] object.
   Therefore, this object must be unique: that is, if [x.content] is [Link _]
   then the element [x] must uniquely own this [Link] object.

   This property is true. This can be seen as follows. A [Link] object is
   installed in the [content] field by [union], where a CAS instruction
   replaces a [Root] object with a [Link] object. Thereafter, the atomic field
   [content] is no longer modified. Indeed, every CAS instruction in the code
   applies to a [Root] object. *)

type 'a content =
  | Root of { value : 'a }
  | Link of { mutable parent : 'a elem }

(* The type ['a elem] represents a vertex in the union-find data structure. *)

(* Every vertex as opposed to only a root vertex, carries an identifier.
   Indeed, identifiers are used, during path compression, to prevent the
   creation of cycles. *)

(* A vertex contains a mutable pointer to a content. This field is atomic. *)

and 'a elem =
  { id : int; mutable content : 'a content [@atomic] }

(* -------------------------------------------------------------------------- *)

(* One way of generating unique identifiers is to use a single generator,
   which is shared by all domains. *)

module SharedGeneratorOfUniqueIds = struct

  let next =
    Atomic.make 0

  let fresh () =
    Atomic.fetch_and_add next 1

end

(* In order to obtain balanced forests, we want the ordering of identifiers
   to be random (while preserving the property that identifiers are unique).

   To ensure this, we combine a unique identifier (in the least significant
   bits) and a random number (in the most significant bits). *)

module G = struct

  include SharedGeneratorOfUniqueIds

  let () =
    assert (Sys.word_size = 64)

  let fresh () =
    (* Generate a unique identifier. *)
    let id = fresh() in
    (* Generate a random number of, say, 12 bits. *)
    let salt = Random.int 4096 in
    (* Combine the two. *)
    let salt = salt lsl (63 - 12) in
    salt lor id

end

(* -------------------------------------------------------------------------- *)

(* [make v] creates a new root. *)

let make (v : 'a) : 'a elem =
  let id = G.fresh()
  and content = Root { value = v } in
  { id; content }

(* -------------------------------------------------------------------------- *)

(* [find x] attempts to find the representative vertex of the equivalence
   class of [x]. It does so by following the path from [x] towards its
   ancestors. Because of interference with other threads, it does not always
   return a root vertex, but it always returns a vertex [z] that lies in the
   same equivalence class as [x] and such that [x.id >= z.id] holds. *)

let rec find (x : 'a elem) : 'a elem =
  match x.content with (* atomic access *)
  | Root _ ->
      x
  | Link { parent = y } ->
      find y

(* [compress x z] performs path compression, starting at [x], ending at [z].

   Because the path from [x] to [z] can be concurrently destroyed by another
   thread, there is no guarantee that the vertex [z] is actually reached. Path
   compression continues as long as the invariant can be maintained: a parent
   must have a smaller identifier than its child.

   Once finished, [compress x z] returns [z]. *)

let rec compress x z =
  match x.content with (* atomic access *)
  | Root _ ->
      (* [x] is a root. Stop. *)
      z
  | Link link ->
      let y = link.parent in
      (* There is an edge of [x] to [y]. *)
      assert (x.id > y.id);
      if y.id > z.id then
        (* Replace the edge of [x] to [y] with an edge from [x] to [z].
           This is beneficial (unless there is interference by another
           thread) and preserves the invariant. *)
        let () = assert (x.id > z.id) in
        link.parent <- z;
        compress y z
      else
        (* Stop. *)
        z

(* [findc x] behaves like [find x] and performs path compression. *)

(* A simple version of it could be defined as follows:

   let findc (x : 'a elem) : 'a elem =
     let z = find x in
     compress x z

   We optimize the common case where [x] is a root. *)

let[@inline] findc (x : 'a elem) : 'a elem =
  match x.content with (* atomic access *)
  | Root _ ->
      x
  | Link { parent = y } ->
      let z = find y in
      compress x z

(* -------------------------------------------------------------------------- *)

(* [get x] returns the value stored at [x]'s representative vertex. *)

(* The linearization point is the atomic read whose result is [Root _]. *)

let rec get (x : 'a elem) : 'a =
  let x = findc x in
  match x.content with (* atomic access *)
  | Root root ->
      (* We have reached the root. Success. *)
      root.value
  | Link _ ->
      (* There has been interference. Continue. *)
      get x

(* -------------------------------------------------------------------------- *)

(* [set x] updates the value stored at [x]'s representative vertex. *)

(* The linearization point is the successful CAS. *)

let rec set (x : 'a elem) (cx' : 'a content) : unit =
  let x = findc x in
  let cx = x.content in (* atomic access *)
  match cx with
  | Root _ ->
    if cas [%atomic.loc x.content] cx cx' then
      (* We have reached and updated the root. Success. *)
      ()
    else
      set x cx'
  | _ ->
      (* There has been interference. Continue. *)
      set x cx'

let[@inline] set (x : 'a elem) (v : 'a) : unit =
  let cx' = Root { value = v } in
  set x cx'

(* -------------------------------------------------------------------------- *)

(* [update x] updates the value stored at [x]'s representative vertex. *)

(* The linearization point is the successful CAS. *)

let rec update (x : 'a elem) (f : 'a -> 'a) : unit =
  let x = findc x in
  let cx = x.content in (* atomic access *)
  match cx with
  | Root { value = v } ->
    if cas [%atomic.loc x.content] cx (Root { value = f v }) then
      (* We have reached and updated the root. Success. *)
      ()
    else
      update x f
  | _ ->
      (* There has been interference. Continue. *)
      update x f

(* -------------------------------------------------------------------------- *)

(* [union x y] merges the equivalence classes of [x] and [y] by installing a
   link from one root vertex to the other. *)

(* The linearization point is the successful CAS. *)

let rec union (x : 'a elem) (y : 'a elem) : 'a option =
  (* Follow the paths out of [x] and [y] as far as possible. *)
  let x = findc x
  and y = findc y in
  if x == y then
    (* [x] and [y] are the same vertex. *)
    None
  else
    (* [x] and [y] are distinct vertices.
       They must have distinct identifiers. *)
    let () = assert (x.id <> y.id) in
    if x.id > y.id then
      (* If [x] is a root, and if we are able to to create an edge
         from [x] to [y], then declare success. There is no need to
         ensure that [y] is a root. Otherwise, try again. *)
      let cx = x.content in (* atomic access *)
      match cx with
      | Root { value = v } ->
        if cas [%atomic.loc x.content] cx (Link { parent = y }) then
          Some v
        else
          union x y
      | _ ->
          union x y
    else
      (* This case is symmetric. *)
      let cy = y.content in (* atomic access *)
      match cy with
      | Root { value = v } ->
        if cas [%atomic.loc y.content] cy (Link { parent = x }) then
          Some v
        else
          union x y
      | _ ->
          union x y

let[@inline] union (x : 'a elem) (y : 'a elem) : 'a option =
  if x == y then None else union x y

(* -------------------------------------------------------------------------- *)

(* [eq x y] determines whether the vertices [x] and [y] belong in the same
   equivalence class. *)

(* We follow Anderson and Woll's algorithm, as presented by Jayanti and
   Tarjan. *)

let rec eq (x : 'a elem) (y : 'a elem) : bool =
  x == y ||
  match x.content with (* atomic access *)
  | Root _ ->
      (* This case is subtle. [x] and [y] are distinct vertices. At the time
         where each of these vertices was found by [findc], it was a root.
         Furthermore, [x] is still a root now, so it has been a root all along.
         Therefore, at the point in time where [y] was found, both [x] and [y]
         were roots. Therefore, we can linearize this operation at that point in
         time, and return [false]. *)
      false
  | Link { parent = x } ->
      (* There has been interference. Continue. *)
      continue_eq x y

and continue_eq (x : 'a elem) (y : 'a elem) : bool =
  (* Note: find [x] first. Order matters here. *)
  let x = findc x in
  let y = findc y in
  eq x y

let[@inline] eq (x : 'a elem) (y : 'a elem) : bool =
  x == y || continue_eq x y
