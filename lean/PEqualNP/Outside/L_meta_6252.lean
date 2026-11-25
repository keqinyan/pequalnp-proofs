import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset

namespace PEqualNP.Outside.L_meta_6252_aux

abbrev V := Fin 21

def seeds : List Nat := [0, 1, 3, 7, 15, 19, 23, 31, 95, 389, 1369, 1371, 5501, 6799, 54781, 503803, 2097151]
abbrev incident (p l : V) := p - l ∈ ([0,1,4,14,16] : List V)

-- A cyclic shift and a second collineation generate all the images needed here.
def step (b : Bool) (i : V) : V :=
  if b then ([0, 10, 7, 3, 18, 1, 4, 2, 11, 14, 9, 8, 5, 15, 12, 20, 17, 6, 19, 16, 13] : List V).getD i.val 0 else i + 1

def Preserves (f : V → V) : Prop :=
  ∀ l : V, ∃ k : V, ∀ i : V, incident i l ↔ incident (f i) k

theorem stepPermutes : ∀ b : Bool, Function.Bijective (step b) := by decide +kernel

theorem stepPreserves : ∀ b : Bool, Preserves (step b) := by
  unfold Preserves
  decide +kernel

def applyWord : List Bool → V → V
  | [], i => i
  | b :: bs, i => applyWord bs (step b i)

theorem wordPermutes (w : List Bool) : Function.Bijective (applyWord w) := by
  induction w with
  | nil => exact Function.bijective_id
  | cons b _ ih => exact ih.comp (stepPermutes b)

theorem wordPreserves (w : List Bool) : Preserves (applyWord w) := by
  induction w with
  | nil => exact fun l => ⟨l, fun _ => Iff.rfl⟩
  | cons b tail ih =>
    intro l
    obtain ⟨k, hk⟩ := stepPreserves b l
    obtain ⟨m, hm⟩ := ih k
    exact ⟨m, fun i => (hk i).trans (hm (step b i))⟩

-- Each entry gives a target representative and a word in the two generators.
-- The highest set bit ends the word. Read the other bits from low to high.
def certificates : List (List (Nat × Nat)) := [
  [(0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1), (0,1)],
  [(0,1), (1,1), (1,1), (1,1), (1,1), (0,1), (1,1), (0,1), (1,1), (1,1), (1,1), (1,1), (1,1), (1,1), (1,1), (1,1), (1,1), (0,1), (1,1), (1,1), (0,1)],
  [(0,1), (1,1), (3,1), (3,1), (3,1), (1,87), (1,1), (1,87), (1,1), (3,1), (3,1), (3,1), (3,1), (3,1), (3,1), (3,1), (3,1), (1,87), (1,1), (3,1), (1,87)],
  [(1,68), (1,1), (3,1), (7,1), (7,1), (3,204), (3,560), (1,87), (3,560), (3,1), (7,1), (7,1), (7,1), (7,1), (7,1), (7,1), (7,1), (3,204), (3,560), (3,1), (3,204)],
  [(3,102), (3,354), (3,1), (7,1), (15,1), (7,853), (7,784), (3,280), (3,560), (7,1419), (7,1), (15,1), (15,1), (15,1), (15,1), (15,1), (15,1), (7,853), (7,784), (7,1419), (3,204)],
  [(0,1), (3,396), (19,1), (3,1), (3,1), (3,177), (3,396), (3,177), (3,396), (3,1), (19,1), (3,1), (19,1), (19,1), (19,1), (19,1), (19,1), (3,177), (3,396), (19,1), (3,177)],
  [(1,68), (3,396), (19,1), (7,1), (7,1), (7,1521), (7,1122), (3,177), (7,1122), (3,1), (23,1), (7,1), (23,1), (23,1), (23,1), (23,1), (23,1), (7,1521), (7,1122), (19,1), (7,1521)],
  [(3,102), (7,610), (19,1), (7,1), (15,1), (15,853), (15,1122), (7,392), (7,1122), (7,1419), (23,1), (15,1), (31,1), (31,1), (31,1), (31,1), (31,1), (15,853), (15,1122), (23,392), (7,1521)],
  [(19,98), (15,1317), (19,1), (15,10811), (31,25073), (15,853), (15,1122), (15,3716), (15,1009), (15,4982), (31,1521), (15,1), (95,1), (31,1), (95,1), (95,1), (95,1), (31,5188), (31,4425), (31,7975), (15,1521)],
  [(19,452), (19,153), (19,153), (19,560), (19,468), (19,452), (19,560), (0,1), (19,468), (19,153), (389,1), (389,1), (19,560), (19,468), (19,560), (19,468), (389,1), (19,452), (389,1), (19,153), (19,452)],
  [(15,2591), (1369,1), (15,1914), (15,1240), (15,1221), (15,3697), (15,9738), (15,3112), (15,2918), (15,1723), (15,241), (15,686), (1369,1), (15,12496), (1369,1), (15,1317), (1369,1), (15,2748), (1369,1), (1369,1), (15,2216)],
  [(15,2591), (1369,1), (31,21769), (31,25068), (31,2360), (31,12986), (15,9738), (31,23766), (15,2918), (31,26982), (31,1353), (31,4737), (1371,1), (31,4408), (1371,1), (31,7975), (1371,1), (31,14411), (1369,1), (1371,1), (31,13577)],
  [(1371,1616), (1371,4644), (95,2939), (1371,1246), (95,4020), (95,1616), (1371,3532), (95,4644), (95,4965), (95,2126), (95,8014), (95,2538), (1371,99), (1371,672), (5501,1), (1371,3862), (5501,1), (95,1297), (5501,1), (1371,561), (1371,2390)],
  [(95,10868), (95,8003), (95,758), (95,664), (6799,1), (95,12931), (95,3365), (389,136), (389,3), (95,2000), (95,2869), (95,7259), (95,1344), (6799,1), (95,5379), (6799,1), (95,7605), (95,3232), (95,1814), (95,1857), (95,4116)],
  [(5501,5), (5501,3171), (5501,730), (5501,2934), (5501,81), (5501,940), (5501,275), (6799,374), (5501,273), (5501,7600), (6799,49), (6799,3), (5501,1297), (5501,17), (5501,1), (5501,552), (54781,1), (5501,522), (54781,1), (5501,84), (5501,1172)],
  [(54781,418), (54781,145), (54781,61), (54781,365), (54781,86), (54781,208), (54781,116), (54781,386), (54781,107), (54781,33), (54781,363), (54781,188), (54781,49), (54781,159), (54781,99), (54781,308), (54781,20), (54781,443), (54781,84), (503803,1), (54781,42)],
  [(503803,9), (503803,31), (503803,20), (503803,10), (503803,5), (503803,19), (503803,15), (503803,28), (503803,14), (503803,7), (503803,22), (503803,11), (503803,12), (503803,6), (503803,3), (503803,16), (503803,8), (503803,4), (503803,2), (503803,1), (503803,18)]]

def entry (j : Fin 17) (l : V) := (certificates.getD j.val []).getD l.val (0,1)
def word (code : Nat) : List Bool := (List.range code.log2).map code.testBit

set_option maxRecDepth 32000 in
set_option maxHeartbeats 2000000 in
theorem certificatesValid : ∀ (j : Fin 17) (l : V),
    (entry j l).1 ∈ seeds ∧ ∀ p : V,
      ((seeds.getD j.val 0).testBit p.val && !decide (incident p l)) =
      (entry j l).1.testBit (applyWord (word (entry j l).2) p).val := by
  decide +kernel

end PEqualNP.Outside.L_meta_6252_aux

open PEqualNP.Outside.L_meta_6252_aux

set_option maxRecDepth 32000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_6252 : have x1 : List ℕ := [(0 : ℕ), (1 : ℕ), (3 : ℕ), (7 : ℕ), (15 : ℕ), (19 : ℕ), (23 : ℕ), (31 : ℕ), (95 : ℕ), (389 : ℕ), (1369 : ℕ), (1371 : ℕ), (5501 : ℕ), (6799 : ℕ), (54781 : ℕ), (503803 : ℕ), (2097151 : ℕ)]; have x2 : List (Fin (21 : ℕ)) := [(0 : Fin (21 : ℕ)), (1 : Fin (21 : ℕ)), (4 : Fin (21 : ℕ)), (14 : Fin (21 : ℕ)), (16 : Fin (21 : ℕ))]; let x3 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x3 x4 : Fin (21 : ℕ)) => x3 - x4 ∈ x2; have x4 : Fin (21 : ℕ) ≃ Fin (21 : ℕ) → Prop := fun (x4 : Fin (21 : ℕ) ≃ Fin (21 : ℕ)) => ∀ (x5 : Fin (21 : ℕ)), ∃ (x6 : Fin (21 : ℕ)), ∀ (x7 : Fin (21 : ℕ)), x3 x7 x5 ↔ x3 (x4 x7) x6; ∀ x5 ∈ x1, ∀ (x7 : Fin (21 : ℕ)), ∃ x8 ∈ x1, ∃ (x9 : Fin (21 : ℕ) ≃ Fin (21 : ℕ)), x4 x9 ∧ ∀ (x10 : Fin (21 : ℕ)), (x5.testBit ↑x10 && !Decidable.decide (x3 x10 x7)) = x8.testBit ↑(x9 x10) := by
  change ∀ m ∈ seeds, ∀ l : V, ∃ t ∈ seeds, ∃ g : V ≃ V,
    Preserves g ∧ ∀ p : V, (m.testBit p.val && !decide (incident p l)) = t.testBit (g p).val
  intro m hm l
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hm
  let k : Fin 17 := ⟨j.val, j.isLt⟩
  obtain ⟨hit, image⟩ := certificatesValid k l
  let w := word (entry k l).2
  refine ⟨_, hit, Equiv.ofBijective (applyWord w) (wordPermutes w), wordPreserves w, ?_⟩
  simpa [k, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt] using image
