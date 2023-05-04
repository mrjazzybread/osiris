open Printf

let print msg =
  printf "%s\n%!" msg

let announce msg =
  printf "**** Expected: %s\n%!" msg

let int msg =
  print msg;
  0

let f x y =
  x + y

let (_ : int) =
  announce "right-to-left";
  f (int "left") (int "right")

let (_ : int) =
  announce "right-to-left";
  int "left" + int "right"

let (_ : int) =
  announce "left-to-right";
  let x = int "left"
  and y = int "right" in
  x + y

let g x y =
  let s = x + y in
  fun z -> s + z

let (_ : int) =
  announce "right-to-left";
  g (int "1") (int "2") (int "3")

module Foo = struct

  type foo = { a : int; b : int }

  (* The following two examples show that the order of fields *at the type
     definition site* is what matters. *)

  let (_ : foo) =
    announce "right-to-left";
    { a = int "left"; b = int "right" }

  let (_ : foo) =
    announce "left-to-right";
    { b = int "left"; a = int "right" }

end

open Foo

type bar = { b : int; a : int }

(* The following examples show that the order of fields *at the type
   definition site* is what matters. Type-directed disambiguation influences
   the dynamic semantics. *)

let (_ : foo) =
  announce "right-to-left";
  { a = int "left"; b = int "right" }

let (_ : foo) =
  announce "left-to-right";
  { b = int "left"; a = int "right" }

let (_ : bar) =
  announce "left-to-right";
  { a = int "left"; b = int "right" }

let (_ : bar) =
  announce "right-to-left";
  { b = int "left"; a = int "right" }
