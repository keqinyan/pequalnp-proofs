import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Bits

namespace PEqualNP.Outside.L_meta_5739_aux

abbrev V := Fin 13
def incidence (p l : V) : Prop := ∃ d ∈ ({0, 1, 3, 9} : Finset V), p = l + d
def free (S : Finset V) (l : V) : Prop := ∀ p ∈ S, ¬incidence p l
def freeSet (S : Finset V) : Finset V :=
  Finset.univ.filter fun l => ∀ p ∈ S, ¬(∃ d ∈ ({0,1,3,9} : Finset V), p = l+d)

def line (l : V) : Nat := ([523, 1046, 2092, 4184, 177, 354, 708, 1416, 2832, 5664, 3137, 6274, 4357] : List Nat).getD l.val 0
def pencil (p : V) : Nat := ([5137, 2083, 4166, 141, 282, 564, 1128, 2256, 4512, 833, 1666, 3332, 6664] : List Nat).getD p.val 0

theorem incidenceBits : ∀ p l : V,
    (incidence p l ↔ (line l).testBit p.val = true) ∧
    (incidence p l ↔ (pencil p).testBit l.val = true) := by
  unfold incidence
  decide +kernel

def bits (a : Nat) : Finset V := Finset.univ.filter fun i : V => a.testBit i.val

theorem inBits (a : Nat) (v : V) : v ∈ bits a ↔ a.testBit v.val = true := by simp [bits]

def pack : List Bool → Nat
  | [] => 0
  | b :: bs => Nat.bit b (pack bs)

theorem packBit : ∀ (xs : List Bool) (n : Nat), (pack xs).testBit n = xs.getD n false
  | [], k => by simp [pack]
  | b :: bs, 0 => by simp [pack]
  | b :: bs, k+1 => by simp [pack, Nat.testBit_bit_succ, packBit bs k]

theorem packBound (xs : List Bool) : pack xs < 2^xs.length := by
  induction xs with
  | nil => decide
  | cons b bs ih => cases b <;> simp [pack, Nat.bit, Nat.pow_succ] <;> omega

theorem represent (S : Finset V) : ∃ m : Fin 8192, bits m.val = S := by
  let xs := List.ofFn fun i : V => decide (i ∈ S)
  have hb : pack xs < 8192 := by simpa [xs] using packBound xs
  refine ⟨⟨pack xs,hb⟩, ?_⟩
  ext i
  rw [inBits, packBit]
  have hi : i.val < xs.length := by simpa [xs] using i.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp only [xs, Option.getD_some, List.getElem_ofFn, decide_eq_true_eq]

theorem disjointBits (a b : Nat) (ha : a < 2^13) :
    a &&& b = 0 ↔ ∀ i : V, a.testBit i.val = true → b.testBit i.val = false := by
  constructor
  · intro hz i hi
    have h := congrArg (fun n : Nat => n.testBit i.val) hz
    simpa [hi] using h
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 13
    · cases hc : a.testBit i with
      | false => simp [hc]
      | true => simp [hc,h ⟨i,hi⟩ hc]
    · have bound : a < 2^i := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega))
      simp [Nat.testBit_lt_two_pow bound]

theorem subsetBit {a b k : Nat} (h : a &&& b = a) (hi : a.testBit k = true) :
    b.testBit k = true := by
  have same := congrArg (fun n : Nat => n.testBit k) h
  simpa [hi] using same

-- Compute all lines missed by a set of points. The low 13 bits encode the line set.
def missing (m : Fin 8192) : Nat :=
  let p := m.val
  let rot := fun d : Nat => ((p >>> d) ||| (p <<< (13-d))) % 8192
  8191 ^^^ (p ||| rot 1 ||| rot 3 ||| rot 9)

-- Using two finite indices keeps the kernel's enumeration depth small.
def rowIndex (hi : Fin 32) (lo : Fin 256) : Fin 8192 :=
  ⟨hi.val * 256 + lo.val, by omega⟩

theorem byBlocks (P : Fin 8192 → Prop) (h : ∀ hi lo, P (rowIndex hi lo)) : ∀ m, P m := by
  intro m
  let hi : Fin 32 := ⟨m.val / 256, by omega⟩
  let lo : Fin 256 := ⟨m.val % 256, by omega⟩
  have eq : rowIndex hi lo = m := Fin.ext (by dsimp [rowIndex, hi, lo]; omega)
  exact eq ▸ h hi lo

set_option maxRecDepth 32000 in
set_option maxHeartbeats 2000000 in
theorem missingBits : ∀ (m : Fin 8192) (l : V),
    (missing m).testBit l.val = decide (m.val &&& line l = 0) := by
  apply byBlocks
  decide +kernel

theorem missingSpec (m : Fin 8192) (l : V) : (missing m).testBit l.val = true ↔ free (bits m) l := by
  rw [missingBits, decide_eq_true_eq, disjointBits _ _ m.isLt]
  constructor
  · intro h p hp inc
    have v := h p ((inBits _ _).1 hp)
    exact Bool.noConfusion (v.symm.trans ((incidenceBits p l).1.1 inc))
  · intro h p hp
    apply Bool.eq_false_iff.mpr
    exact fun inc => h p ((inBits _ _).2 hp) ((incidenceBits p l).1.2 inc)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 2000000 in
theorem finiteCases : ∀ m : Fin 8192,
    (∃ p : V, m.val.testBit p.val = false ∧ missing m &&& pencil p = 0) ∨
    (∃ l : V, m.val &&& line l = m.val) ∨
    (∃ p : V, missing m &&& pencil p = missing m) ∨
    (bits m.val).card = 3 ∨ (bits (missing m)).card = 3 := by
  apply byBlocks
  decide +kernel

theorem classify (S : Finset V)
    (closed : ∀ p ∉ S, ∃ l : V, free S l ∧ incidence p l)
    (generic : ¬((∃ l : V, ∀ p ∈ S, incidence p l) ∨ (∃ p : V, ∀ l : V, free S l → incidence p l))) :
    S.card = 3 ∨ (freeSet S).card = 3 := by
  obtain ⟨m, rfl⟩ := represent S
  rcases finiteCases m with ⟨p,absent,miss⟩ | ⟨l,h⟩ | ⟨p,h⟩ | small | small
  · have hp : p ∉ bits m.val := by simp [inBits, absent]
    obtain ⟨l,hl,hpl⟩ := closed p hp
    have hl' := (missingSpec m l).2 hl
    have hi := (incidenceBits p l).2.1 hpl
    have bad := congrArg (fun n : Nat => n.testBit l.val) miss
    simp [hl',hi] at bad
  · exact (generic (.inl ⟨l,fun p hp => (incidenceBits p l).1.2 (subsetBit h ((inBits _ _).1 hp))⟩)).elim
  · exact (generic (.inr ⟨p,fun l hl => (incidenceBits p l).2.2 (subsetBit h ((missingSpec m l).2 hl))⟩)).elim
  · exact Or.inl small
  · right
    have eq : freeSet (bits m.val) = bits (missing m) := by
      ext l
      rw [inBits,missingSpec]
      simp only [freeSet,Finset.mem_filter, Finset.mem_univ,true_and, free, incidence]
    simpa [eq] using small

end PEqualNP.Outside.L_meta_5739_aux

open PEqualNP.Outside.L_meta_5739_aux

set_option maxRecDepth 32000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_5739 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), x3 x4 x7 ∧ x2 x5 x7; have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => (∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x5, x2 x7 x6) ∨ ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x3 x5 x7 → x2 x6 x7; ∀ (x6 : Finset (Fin (13 : ℕ))), x4 x6 → ¬x5 x6 → x6.card = (3 : ℕ) ∨ ∃ (x9 : Finset (Fin (13 : ℕ))), x9.card = (3 : ℕ) ∧ ∀ (x10 : Fin (13 : ℕ)), x10 ∈ x9 ↔ x3 x6 x10 := by
  dsimp only
  intro S hc hn
  rcases classify S hc hn with small | small
  · exact Or.inl small
  · refine Or.inr ⟨_, small, ?_⟩
    intro l
    simp only [freeSet, Finset.mem_filter, Finset.mem_univ, true_and]
