import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_764

abbrev g3 : (Fin 3 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

abbrev f5 : (Fin 5 → Bool) → Bool := fun x => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)

abbrev F5 : (Fin 5 → Bool) → Bool := fun x => (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || g3 (fun j : Fin 3 => x (Fin.natAdd 2 j))

theorem hnc : ∃ y y' : Fin 3 → Bool, g3 y ≠ g3 y' := ⟨fun _ => true, fun _ => false, by decide⟩

theorem hfeq : ∀ x : Fin 5 → Bool, f5 x = F5 x := by decide

theorem hFF : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 F5 (t + 2) ↔ PEqualNP.MetaComplexity.HasCircuitSize 5 f5 (t + 2) := by
  intro t
  constructor
  · intro h
    obtain ⟨C, h1, h2, h3⟩ := h
    exact ⟨C, h1, h2, fun x => by rw [hfeq x]; exact h3 x⟩
  · intro h
    obtain ⟨C, h1, h2, h3⟩ := h
    exact ⟨C, h1, h2, fun x => by rw [← hfeq x]; exact h3 x⟩

theorem key : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 f5 (t + 2) ↔ 6 ≤ t + 2 := by
  intro t
  have h1 := PEqualNP.MetaComplexity.L153 3 t g3 hnc
  have h2 := PEqualNP.MetaComplexity.L100 t
  have e1 : PEqualNP.MetaComplexity.HasCircuitSize 5 F5 (t + 2) ↔ PEqualNP.MetaComplexity.HasCircuitSize 3 g3 t := h1
  have e2 : PEqualNP.MetaComplexity.HasCircuitSize 3 g3 t ↔ 4 ≤ t := h2
  exact (hFF t).symm.trans (e1.trans (e2.trans (by omega : (4 ≤ t) ↔ 6 ≤ t + 2)))

end PEqualNP.Outside.L_meta_764

open PEqualNP.Outside.L_meta_764 in
theorem PEqualNP.Outside.L_meta_764 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s := by
  intro s
  by_cases hs : 2 ≤ s
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, s = t + 2 := ⟨s - 2, by omega⟩
    exact key t
  · constructor
    · intro h
      have h3 : PEqualNP.MetaComplexity.HasCircuitSize 5 f5 3 := by
        obtain ⟨C, h1, h2, h3⟩ := h
        exact ⟨C, h1, by omega, h3⟩
      have h6 := (key 1).mp h3
      omega
    · intro h
      omega
