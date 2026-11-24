import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_765

abbrev g4 : (Fin 4 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0)

abbrev f6 : (Fin 6 → Bool) → Bool := fun x => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)

abbrev F6 : (Fin 6 → Bool) → Bool := fun x => (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) || g4 (fun j : Fin 4 => x (Fin.natAdd 2 j))

theorem hnc : ∃ y y' : Fin 4 → Bool, g4 y ≠ g4 y' := ⟨fun _ => true, fun _ => false, by decide⟩

theorem hfeq : ∀ x : Fin 6 → Bool, f6 x = F6 x := by decide

theorem hFF : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 F6 (t + 2) ↔ PEqualNP.MetaComplexity.HasCircuitSize 6 f6 (t + 2) := by
  intro t
  constructor
  · intro h
    obtain ⟨C, h1, h2, h3⟩ := h
    exact ⟨C, h1, h2, fun x => by rw [hfeq x]; exact h3 x⟩
  · intro h
    obtain ⟨C, h1, h2, h3⟩ := h
    exact ⟨C, h1, h2, fun x => by rw [← hfeq x]; exact h3 x⟩

theorem key : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 f6 (t + 2) ↔ 5 ≤ t + 2 := by
  intro t
  have h1 := PEqualNP.MetaComplexity.L153 4 t g4 hnc
  have h2 := PEqualNP.MetaComplexity.L112 t
  have e1 : PEqualNP.MetaComplexity.HasCircuitSize 6 F6 (t + 2) ↔ PEqualNP.MetaComplexity.HasCircuitSize 4 g4 t := h1
  have e2 : PEqualNP.MetaComplexity.HasCircuitSize 4 g4 t ↔ 3 ≤ t := h2
  exact (hFF t).symm.trans (e1.trans (e2.trans (by omega : (3 ≤ t) ↔ 5 ≤ t + 2)))

end PEqualNP.Outside.L_meta_765

open PEqualNP.Outside.L_meta_765 in
theorem PEqualNP.Outside.L_meta_765 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔ 5 ≤ s := by
  intro s
  by_cases hs : 2 ≤ s
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, s = t + 2 := ⟨s - 2, by omega⟩
    exact key t
  · constructor
    · intro h
      have h3 : PEqualNP.MetaComplexity.HasCircuitSize 6 f6 3 := by
        obtain ⟨C, h1, h2, h3⟩ := h
        exact ⟨C, h1, by omega, h3⟩
      have h5 := (key 1).mp h3
      omega
    · intro h
      omega
