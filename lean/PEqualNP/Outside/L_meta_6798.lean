import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset

set_option maxRecDepth 32000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_6798 : have x1 : ℕ → Fin (13 : ℕ) → ℕ → Bool → Fin (26 : ℕ) → Bool := fun (x1 : ℕ) (x2 : Fin (13 : ℕ)) (x3 : ℕ) (x4 : Bool) (x5 : Fin (26 : ℕ)) => x1.testBit (((if x4 = Bool.true then (13 : ℕ) - x3 else x3) * ↑x5 + ↑x2) % (13 : ℕ) + (13 : ℕ) * if x4 = Bool.true then (1 : ℕ) - ↑x5 / (13 : ℕ) else ↑x5 / (13 : ℕ)); ∀ x2 ∈ [(7405575 : ℕ), (23330829 : ℕ), (5799955 : ℕ), (22282261 : ℕ), (21757977 : ℕ), (21233693 : ℕ), (19415081 : ℕ), (5275731 : ℕ)],   ∀ (x4 : Fin (13 : ℕ)),     ∀ x5 ∈ [(1 : ℕ), (3 : ℕ), (9 : ℕ)],       ∀ (x7 : Bool),         have x8 : Finset (Fin (13 : ℕ)) := {x8 : Fin (13 : ℕ) | x1 x2 x4 x5 x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true};         have x9 : Finset (Fin (13 : ℕ)) := {x9 : Fin (13 : ℕ) | x1 x2 x4 x5 x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true};         let x10 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x10 x11 : Fin (13 : ℕ)) => x10 = x11 ∨ x10 = x11 + (1 : Fin (13 : ℕ)) ∨ x10 = x11 + (3 : Fin (13 : ℕ)) ∨ x10 = x11 + (9 : Fin (13 : ℕ));         (∀ x11 ∈ x8, ∀ x13 ∈ x9, ¬x10 x11 x13) ∧ (∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x8 | x10 x12 x11}.card ≤ (2 : ℕ)) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x9 | x10 x11 x12}.card ≤ (2 : ℕ) := by
  dsimp only
  intro mask hm shift scale hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm hs
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl <;> revert shift <;> decide +kernel
