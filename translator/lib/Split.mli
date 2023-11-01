val split : (string -> unit) ->
            (string -> unit) ->
	    [`Split | `NoSplit] list ->
            OsirisAst.ast ->
            OsirisAst.ast DAG.t
