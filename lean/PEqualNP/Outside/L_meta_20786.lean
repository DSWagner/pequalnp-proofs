import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20786

open PEqualNP.CircuitLowerBounds

def c : Circuit := ⟨[ ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [8, 2]⟩, ⟨GateOp.and, [8, 2]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.or, [12, 3]⟩, ⟨GateOp.and, [12, 3]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.or, [16, 4]⟩, ⟨GateOp.and, [16, 4]⟩, ⟨GateOp.not, [18]⟩, ⟨GateOp.and, [17, 19]⟩ ], 20⟩

theorem condC : PEqualNP.MetaComplexity.FanInTwo c := by
  intro g hg
  simp only [c, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
theorem main : ∀ x : Fin 5 → Bool, c.eval (List.ofFn x) = (2523490710 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x) := by
  decide

end PEqualNP.Outside.L_meta_20786

open PEqualNP.Outside.L_meta_20786 in
theorem PEqualNP.Outside.L_meta_20786 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (2523490710 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 16 := ⟨c, condC, by decide, main⟩
