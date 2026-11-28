import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57638.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 12-gate circuit found by SAT-based exact synthesis. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.and, [7, 13]⟩, ⟨GateOp.or, [15, 16]⟩], 17⟩


end PEqualNP.Outside.L_meta_57638.Helpers

theorem PEqualNP.Outside.L_meta_57638 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270649387 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_57638.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_57638.Helpers.witness]
