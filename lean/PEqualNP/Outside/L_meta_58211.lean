import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_58211.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [6, 12]⟩, ⟨GateOp.or, [0, 14]⟩, ⟨GateOp.not, [16]⟩, ⟨GateOp.or, [15, 17]⟩], 18⟩


end PEqualNP.Outside.L_meta_58211.Helpers

theorem PEqualNP.Outside.L_meta_58211 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270550972 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_58211.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_58211.Helpers.witness]
