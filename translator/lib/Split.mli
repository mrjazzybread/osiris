val split : (string -> unit) ->
            (string -> unit) ->
	    Options.splitting_strategy list ->
            OsirisAst.ast ->
            OsirisAst.ast DAG.t
