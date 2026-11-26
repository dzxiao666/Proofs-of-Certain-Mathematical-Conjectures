import PublicConjectures.Geometry

noncomputable section
namespace Shannon

def Rel (q : ℚ) (Y X : ℝ) : Prop := X = 1 - (q:ℝ) + Y - Y/q

private theorem pair_values {a b : ℚ} {Y X : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (h : Rel a Y X) (g : Rel b Y X) :
    Y = (a:ℝ)*b ∧ X = (1-(a:ℝ))*(1-(b:ℝ)) := by
  have ha' : (a:ℝ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b:ℝ) ≠ 0 := by exact_mod_cast hb
  have hab' : (a:ℝ) - b ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab)
  unfold Rel at h g
  field_simp at h g
  have hp : ((a:ℝ)-b)*(Y-(a:ℝ)*b)=0 := by linear_combination (a:ℝ)*g - (b:ℝ)*h
  have hy := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hab')
  refine ⟨hy, ?_⟩
  rw [hy] at h
  apply (mul_right_cancel₀ ha')
  linear_combination h

private theorem distinct_three {a b d : ℚ} {Y X : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (h : Rel a Y X) (g : Rel b Y X) (f : Rel d Y X) : False := by
  have one := (pair_values ha hb hab h g).1
  have two := (pair_values ha hd had h f).1
  have ha' : (a:ℝ) ≠ 0 := by exact_mod_cast ha
  exact hbd (by exact_mod_cast mul_left_cancel₀ ha' (one.symm.trans two))

private theorem mixed {c X Z Y : ℝ} {a b d : ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (h : Rel a Y X) (g : Rel b Y X) (f : Rel d Y Z)
    (eq : X+Z = 1+2*c*Y) : ∃ q : ℚ, (q:ℝ) = 2*c := by
  obtain ⟨hy,hx⟩ := pair_values ha hb hab h g
  refine ⟨((1-a)*(1-b) + (1-d+a*b-a*b/d) - 1)/(a*b), ?_⟩
  push_cast
  have hy' : (a:ℝ)*b ≠ 0 := by exact_mod_cast (mul_ne_zero ha hb)
  apply (div_eq_iff hy').2
  unfold Rel at f
  rw [← hy, ← hx, ← f]
  linarith

def Fits (c X Y : ℝ) (e : Bool × ℚ) := Rel e.2 Y (if e.1 then 1+2*c*Y-X else X)

theorem rational_of_triple {c X Y : ℝ} {a b d : Bool × ℚ}
    (ha : a.2 ≠ 0) (hb : b.2 ≠ 0) (hd : d.2 ≠ 0)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (h : Fits c X Y a) (g : Fits c X Y b) (f : Fits c X Y d) :
    ∃ q : ℚ, (q:ℝ) = 2*c := by
  obtain ⟨A,a⟩ := a; obtain ⟨B,b⟩ := b; obtain ⟨D,d⟩ := d
  cases A <;> cases B <;> cases D <;>
    simp [Fits] at * <;>
    first
    | exact (distinct_three ha hb hd hab had hbd h g f).elim
    | exact mixed ha hb hab h g f (by ring)
    | exact mixed ha hd had h f g (by ring)
    | exact mixed hb hd hbd g f h (by ring)

end Shannon
