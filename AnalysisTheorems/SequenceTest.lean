import AnalysisTheorems.Sequences

example : seq_is_limit (fun n => 6) 6 := by
  intro ε hε
  use 6
  simp [hε]
