import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3037 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2],   have x4 : Finset (Fin x1) → Fin (x1 + x1) → Bool := fun (x4 : Finset (Fin x1)) (x5 : Fin (x1 + x1)) => Fin.addCases (fun (x6 : Fin x1) => Decidable.decide ¬∃ x7 ∈ x4, x2 x6 x7) (fun (x6 : Fin x1) => Decidable.decide (x6 ∈ x4)) x5;   ∀ (x5 : Finset (Fin x1)), Fintype.card { x6 : Fin x1 // x4 x5 (Fin.natAdd x1 x6) = Bool.true } = x5.card ∧ ¬∃ (x6 : Fin x1) (x7 : Fin x1), x2 x6 x7 ∧ x4 x5 (Fin.castAdd x1 x6) = Bool.true ∧ x4 x5 (Fin.natAdd x1 x7) = Bool.true := by
  intro x1 x2 x3 x4 x5
  constructor
  · have h : ∀ x6 : Fin x1, x4 x5 (Fin.natAdd x1 x6) = Bool.true ↔ x6 ∈ x5 := by
      intro x6
      dsimp only [x4]
      rw [Fin.addCases_right]
      simp
    exact (Fintype.card_congr (Equiv.subtypeEquivRight h)).trans (Fintype.card_coe x5)
  · rintro ⟨x6, x7, hrel, hleft, hright⟩
    dsimp only [x4] at hleft hright
    rw [Fin.addCases_left] at hleft
    rw [Fin.addCases_right] at hright
    simp only [decide_eq_true_eq, not_exists, not_and] at hleft hright
    exact hleft x7 hright hrel
