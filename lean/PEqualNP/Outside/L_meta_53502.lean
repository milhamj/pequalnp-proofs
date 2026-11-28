import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53502.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [12, 14]⟩, ⟨GateOp.or, [10, 15]⟩, ⟨GateOp.and, [13, 17]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.or, [4, 19]⟩], 20⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_53502.Helpers

theorem PEqualNP.Outside.L_meta_53502 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816121 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨PEqualNP.Outside.L_meta_53502.Helpers.witness, PEqualNP.Outside.L_meta_53502.Helpers.mono, by decide, by decide +kernel⟩
