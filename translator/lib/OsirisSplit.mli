val split : (string -> unit) ->
            (string -> unit) ->
	    Options.splitting_strategy ->
            string -> OsirisAst.ast ->
            (string option * OsirisAst.ast) DAG.t
