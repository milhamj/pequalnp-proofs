import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57401.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 12-gate circuit found by SAT-based exact synthesis. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [15, 16]⟩], 17⟩


end PEqualNP.Outside.L_meta_57401.Helpers

theorem PEqualNP.Outside.L_meta_57401 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2215483 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_57401.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_57401.Helpers.witness]
