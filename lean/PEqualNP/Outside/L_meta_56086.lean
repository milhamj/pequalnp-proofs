import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56086.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.and, [6, 11]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [14, 15]⟩], 16⟩


end PEqualNP.Outside.L_meta_56086.Helpers

theorem PEqualNP.Outside.L_meta_56086 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274844604 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_56086.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_56086.Helpers.witness]
