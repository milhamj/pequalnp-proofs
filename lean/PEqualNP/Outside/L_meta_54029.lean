import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54029.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 10-gate circuit found by SAT-based exact synthesis. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [1, 5]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.or, [11, 14]⟩], 15⟩


end PEqualNP.Outside.L_meta_54029.Helpers

theorem PEqualNP.Outside.L_meta_54029 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2215231 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_54029.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_54029.Helpers.witness]
