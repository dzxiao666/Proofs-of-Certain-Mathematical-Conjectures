import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! Threefold closed-neighbourhood domination on the finite king board (OEIS A379759).
Coordinates are zero-based. A local embedding supplies three distinct occupied squares. -/
namespace Kings

abbrev Cell (m : ℕ) := Fin m × Fin m

def Close (x y : ℕ) : Prop := x ≤ y + 1 ∧ y ≤ x + 1

def Covers (p q : Cell m) : Prop := Close p.1.val q.1.val ∧ Close p.2.val q.2.val

def Triple (s : Finset (Cell m)) : Prop :=
  ∀ p : Cell m, ∃ f : Fin 3 ↪ ↥s, ∀ k, Covers p (f k).val

def Optimal (m n : ℕ) : Prop :=
  (∃ s : Finset (Cell m), Triple s ∧ s.card = n) ∧
    ∀ s : Finset (Cell m), Triple s → n ≤ s.card

private abbrev Index (r : ℕ) := Fin 3 × (Fin (r+1) × Fin (r+1))

private def a (h : 3*r < m) (i : Fin (r+1)) : Fin m :=
  ⟨3*i.val, by have := i.isLt; omega⟩

private def b (h : 3*r < m) (i : Fin (r+1)) : Fin m :=
  ⟨if 3*i.val+1 < m then 3*i.val+1 else 3*i.val-1, by
    have := i.isLt; split <;> omega⟩

private theorem separate (hr : 0 < r) (h : 3*r < m) (i j : Fin (r+1)) :
    a h i ≠ b h j := by
  intro eq
  have v := congrArg Fin.val eq
  simp only [a, b] at v
  split at v <;> omega

private theorem nearest (lo : 3*r < m) (hi : m ≤ 3*r+2) (x : Fin m) :
    ∃ i j : Fin (r+1), Close x.val (a lo i).val ∧ Close x.val (b lo j).val := by
  have hx := x.isLt
  refine ⟨⟨(x.val+1)/3, by omega⟩, ⟨x.val/3, by omega⟩, ?_, ?_⟩
  · simp only [Close, a]; omega
  · simp only [Close, b]; split <;> omega

private def place (lo : 3*r < m) (u : Index r) : Cell m :=
  if u.1.val = 0 then (a lo u.2.1, a lo u.2.2)
  else if u.1.val = 1 then (a lo u.2.1, b lo u.2.2)
  else (b lo u.2.1, a lo u.2.2)

private theorem lower (lo : 3*r < m) (s : Finset (Cell m)) (hs : Triple s) :
    3*(r+1)^2 ≤ s.card := by
  classical
  choose f hf using hs
  let g (u : Index r) : ↥s := f (a lo u.2.1, a lo u.2.2) u.1
  have inj : Function.Injective g := by
    rintro ⟨k,i,j⟩ ⟨l,v,w⟩ eq
    have one := hf (a lo i, a lo j) k
    have two := hf (a lo v, a lo w) l
    change f (a lo i, a lo j) k = f (a lo v, a lo w) l at eq
    rw [← eq] at two
    simp only [Covers, Close, a] at one two
    obtain ⟨⟨h1,h2⟩,h3,h4⟩ := one
    obtain ⟨⟨h5,h6⟩,h7,h8⟩ := two
    have iv : i = v := Fin.ext (by omega)
    have jw : j = w := Fin.ext (by omega)
    subst v; subst w
    have kl := (f _).injective eq
    subst l; rfl
  simpa [Index, pow_two, Nat.mul_assoc] using Fintype.card_le_of_injective g inj

theorem optimal {m r : ℕ} (hr : 0 < r) (lo : 3*r < m) (hi : m ≤ 3*r+2) :
    Optimal m (3*(r+1)^2) := by
  classical
  let s := Finset.univ.image (place lo)
  have hs : Triple s := by
    intro p
    obtain ⟨i,v,hi₀,hv⟩ := nearest lo hi p.1
    obtain ⟨j,w,hj,hw⟩ := nearest lo hi p.2
    let ix (k : Fin 3) : Index r := (k, if k.val = 2 then v else i, if k.val = 1 then w else j)
    let f (k : Fin 3) : ↥s := ⟨place lo (ix k), Finset.mem_image.mpr ⟨ix k, Finset.mem_univ _, rfl⟩⟩
    have disX := separate hr lo i v
    have disY := separate hr lo j w
    have inj : Function.Injective f := by
      intro k l eq
      have he := congrArg Subtype.val eq
      fin_cases k <;> fin_cases l <;> simp_all [f, ix, place, Prod.ext_iff]
    refine ⟨⟨f,inj⟩, ?_⟩
    intro k
    fin_cases k <;> simp_all [f, ix, place, Covers]
  have ub := Finset.card_image_le (s := (Finset.univ : Finset (Index r))) (f := place lo)
  have bound : s.card ≤ 3*(r+1)^2 := by simpa [s, Index, pow_two, Nat.mul_assoc] using ub
  exact ⟨⟨s, hs, Nat.le_antisymm bound (lower lo s hs)⟩, lower lo⟩

/-- Both of the minima in McCarty's observation are 3(r+1)^2. -/
theorem mccarty (r : ℕ) (hr : 0 < r) :
    Optimal (3*r+1) (3*(r+1)^2) ∧ Optimal (3*r+2) (3*(r+1)^2) :=
  ⟨optimal hr (by omega) (by omega), optimal hr (by omega) (by omega)⟩

end Kings
