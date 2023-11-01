val split : (string -> unit) ->
            (string -> unit) ->
	    [`Split | `NoSplit] ->
            string -> OsirisAst.ast ->
            (string option * OsirisAst.ast) DAG.t
