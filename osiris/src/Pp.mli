(* [pretty_printer fmt graph] pretty-prints the elements of [graph]:
   - It writes to [fmt]
   - Print the element [name, doc] prints:
     [ Definition name := doc ].
   - The leaves of [graph] are printed first: if [A] precedes [B] in [graph],
     [A] depends on [B].
 *)
val pretty_printer : (string * string * Preprint.expression) DAG.t ->
                     PPrint.document DAG.t
