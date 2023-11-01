let split _verbose _debug _splitting_strategy
      name osiris_ast: (string option * OsirisAst.ast) DAG.t =
  DAG.init (Some name, osiris_ast)
