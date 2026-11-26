import PublicConjectures.Shannon.Angle

noncomputable section
namespace Shannon
open Real

/-- Projection of vertex i of the regular unit n-gon on the axis with angle φ. -/
def V (n : ℕ) (i : ℤ) (φ : ℝ) := cos ((i:ℝ) * angle n - φ)

/-- Affine coordinates at vertex i, in the basis pointing to its two neighbours. -/
def frame (n : ℕ) (i : ℤ) (x y : ℝ) : ℝ → ℝ := fun φ =>
  V n i φ + x*(V n (i+1) φ - V n i φ) + y*(V n (i-1) φ - V n i φ)

private theorem vertex_proj (n : ℕ) (i : ℤ) (φ : ℝ) :
    V n i φ = V n i 0 * cos φ + V n i (π/2) * sin φ := by
  simp [V,cos_sub]

theorem frame_proj (n : ℕ) (i : ℤ) (x y φ : ℝ) :
    frame n i x y φ = frame n i x y 0 * cos φ + frame n i x y (π/2) * sin φ := by
  unfold frame
  rw [vertex_proj n i φ, vertex_proj n (i+1) φ, vertex_proj n (i-1) φ]
  ring

theorem frame_period (n : ℕ) (hn : 0 < n) (i : ℤ) (x y : ℝ) :
    frame n (i+n) x y = frame n i x y := by
  have h (j : ℤ) (φ : ℝ) : V n (j+n) φ = V n j φ := by
    unfold V; push_cast
    rw [show ((j:ℝ)+n)*angle n - φ = ((j:ℝ)*angle n-φ)+2*π by
      rw [add_mul, angle_mul n hn]; ring, cos_add_two_pi]
  funext φ
  simp only [frame, show i+(n:ℤ)+1 = i+1+n by omega,
    show i+(n:ℤ)-1 = i-1+n by omega, h]

private theorem relative_vertex (n : ℕ) (i j : ℤ) (β : ℝ) :
    V n j ((i:ℝ)*angle n + β) = cos (((j-i:ℤ):ℝ)*angle n - β) := by
  unfold V; push_cast; congr 1; ring

private theorem at_axis (n : ℕ) (i : ℤ) (x y : ℝ) :
    frame n i x y ((i:ℝ)*angle n+0) = 1+(x+y)*(cos (angle n)-1) := by
  simp only [frame,relative_vertex]; simp; ring

private theorem at_perp (n : ℕ) (i : ℤ) (x y : ℝ) :
    frame n i x y ((i:ℝ)*angle n + π/2) = (x-y)*sin (angle n) := by
  simp [frame,relative_vertex,cos_sub]; ring

theorem frame_inj {n : ℕ} (hn : 3 ≤ n) {i : ℤ} {x y X Y : ℝ}
    (h : frame n i x y = frame n i X Y) : x=X ∧ y=Y := by
  obtain ⟨hp,hp'⟩ := angle_bounds hn
  have hs := sin_pos_of_pos_of_lt_pi hp hp'
  have hc := cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ) ≤ 0) hp'.le hp
  rw [cos_zero] at hc
  have h1 := congrFun h ((i:ℝ)*angle n+0)
  have h2 := congrFun h ((i:ℝ)*angle n+π/2)
  rw [at_axis, at_axis] at h1
  rw [at_perp, at_perp] at h2
  have ha := mul_right_cancel₀ (by linarith : cos (angle n)-1 ≠ 0) (add_left_cancel h1)
  have hb := mul_right_cancel₀ hs.ne' h2
  constructor <;> linarith

/-- The exact affine change of basis across one side. -/
theorem frame_next (n : ℕ) (i : ℤ) (x y : ℝ) :
    frame n (i+1) x y = frame n i (1+2*cos (angle n)*x-y) x := by
  funext φ
  have hrec (j : ℤ) : V n (j+1) φ + V n (j-1) φ = 2*cos (angle n)*V n j φ := by
    unfold V; push_cast
    rw [show ((j:ℝ)+1)*angle n-φ = ((j:ℝ)*angle n-φ)+angle n by ring,
        show ((j:ℝ)-1)*angle n-φ = ((j:ℝ)*angle n-φ)-angle n by ring,cos_add,cos_sub ((j:ℝ)*angle n-φ) (angle n)]
    ring
  have ha := hrec i
  have hb := hrec (i+1)
  simp only [add_sub_cancel_right] at hb
  simp only [frame,add_sub_cancel_right]
  linear_combination x * hb - x * ha

private theorem cos_gap_pos {n : ℕ} (hn : 3 ≤ n) {j : ℤ}
    (hj : 1 ≤ j) (hj' : j < n) : cos ((j:ℝ)*angle n) ≤ cos (angle n) := by
  obtain ⟨hp,hp'⟩ := angle_bounds hn
  have ht := angle_mul n (by omega)
  have small (l : ℤ) (h1 : 1 ≤ l) (h2 : 2*l ≤ n) :
      cos ((l:ℝ)*angle n) ≤ cos (angle n) := by
    have ha : (1:ℝ) ≤ l := by exact_mod_cast h1
    have hb : 2*(l:ℝ) ≤ n := by exact_mod_cast h2
    apply cos_le_cos_of_nonneg_of_le_pi hp.le
    · nlinarith [mul_le_mul_of_nonneg_right hb hp.le]
    · nlinarith [mul_le_mul_of_nonneg_right ha hp.le]
  by_cases h : 2*j ≤ n
  · exact small j hj h
  · have h' := small ((n:ℤ)-j) (by omega) (by omega)
    push_cast at h'
    rwa [sub_mul, ht, cos_two_pi_sub] at h'

private theorem cos_gap {n : ℕ} (hn : 3 ≤ n) {j : ℤ}
    (hl : -(n:ℤ) < j) (hr : j < n) (hz : j ≠ 0) :
    cos ((j:ℝ)*angle n) ≤ cos (angle n) := by
  by_cases h : 1 ≤ j
  · exact cos_gap_pos hn h hr
  · simpa using cos_gap_pos hn (j := -j) (by omega) (by omega)

def Near (n : ℕ) (i j : ℤ) : Prop :=
  j=i ∨ j=i+1 ∨ j=i-1 ∨ j+(n:ℤ)=i+1 ∨ j-(n:ℤ)=i-1

theorem near_of_inter {n : ℕ} (hn : 3 ≤ n) {i j : ℤ}
    (hi : 0 ≤ i) (hi' : i < n) (hj : 0 ≤ j) (hj' : j < n)
    {x y X Y : ℝ} (hs : x+y < 1)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hS : X+Y ≤ 1)
    (eq : frame n i x y = frame n j X Y) : Near n i j := by
  by_contra bad
  unfold Near at bad
  have gap (a : ℤ) (ha : j-1 ≤ a) (ha' : a ≤ j+1) :
      V n a ((i:ℝ)*angle n+0) ≤ cos (angle n) := by
    rw [relative_vertex, sub_zero]
    apply cos_gap hn <;> omega
  have g0 := gap j (by omega) (by omega)
  have g1 := gap (j+1) (by omega) (by omega)
  have g2 := gap (j-1) (by omega) (by omega)
  have he := congrFun eq ((i:ℝ)*angle n+0)
  rw [at_axis] at he
  simp only [frame] at he
  have hp := angle_bounds hn
  have hc := cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ) ≤ 0) hp.2.le hp.1
  rw [cos_zero] at hc
  nlinarith [mul_pos (sub_pos.mpr hs) (sub_pos.mpr hc),
    mul_le_mul_of_nonneg_left g1 hX, mul_le_mul_of_nonneg_left g2 hY,
    mul_le_mul_of_nonneg_left g0 (by linarith : 0 ≤ 1-X-Y)]

end Shannon
