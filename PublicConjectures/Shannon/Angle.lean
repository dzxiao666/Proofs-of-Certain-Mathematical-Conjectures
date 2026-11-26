import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

noncomputable section
namespace Shannon
open Real

def angle (n : ℕ) : ℝ := 2 * π / n

theorem angle_bounds {n : ℕ} (hn : 3 ≤ n) : 0 < angle n ∧ angle n < π := by
  have h : (3:ℝ) ≤ n := by exact_mod_cast hn
  unfold angle
  constructor
  · positivity
  · apply (div_lt_iff₀ (by linarith : 0 < (n:ℝ))).2
    nlinarith [Real.pi_pos]

theorem angle_mul (n : ℕ) (hn : 0 < n) : (n:ℝ) * angle n = 2 * π := by
  unfold angle; field_simp

private theorem integral_double_cos {n : ℕ} (hn : 0 < n) :
    IsIntegral ℤ ((2 * cos (angle n) : ℝ) : ℂ) := by
  let z : ℂ := Complex.exp ((angle n : ℂ) * Complex.I)
  let w : ℂ := Complex.exp ((-(angle n) : ℝ) * Complex.I)
  have harg : (n:ℂ) * ((angle n : ℂ) * Complex.I) = 2 * (π:ℂ) * Complex.I := by
    have h := congrArg Complex.ofReal (angle_mul n hn)
    push_cast at h
    linear_combination Complex.I * h
  have hz : z^n = 1 := by
    rw [← Complex.exp_nat_mul, harg, Complex.exp_two_pi_mul_I]
  have hw : w = z⁻¹ := by simp [w,z, ← Complex.exp_neg]
  have h1 : IsIntegral ℤ z := IsIntegral.of_pow hn (hz ▸ isIntegral_one)
  have hw' : w^n = 1 := by rw [hw, inv_pow, hz, inv_one]
  have h2 : IsIntegral ℤ w := IsIntegral.of_pow hn (hw' ▸ isIntegral_one)
  have he : ((2 * cos (angle n) : ℝ) : ℂ) = z + w := by
    apply Complex.ext <;> simp only [z, w, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.add_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Real.cos_neg, Real.sin_neg] <;> ring
  rw [he]; exact h1.add h2

theorem exceptional_of_rat {n : ℕ} (hn : 3 ≤ n)
    (hr : ∃ q : ℚ, (q:ℝ) = 2 * cos (angle n)) : n = 3 ∨ n = 4 ∨ n = 6 := by
  obtain ⟨q,hq⟩ := hr
  have hInt := integral_double_cos (n := n) (by omega)
  rw [← hq] at hInt
  have hqInt : IsIntegral ℤ q := by
    apply (isIntegral_algebraMap_iff (R := ℤ) (B := ℂ) (algebraMap ℚ ℂ).injective).1
    simpa using hInt
  letI : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  obtain ⟨j,hj⟩ := (IsIntegrallyClosed.isIntegral_iff (K := ℚ)).mp hqInt
  have he : (j:ℝ) = 2 * cos (angle n) := by
    calc (j:ℝ) = ((q:ℚ):ℝ) := by exact_mod_cast hj
         _ = _ := hq
  by_contra! h
  have hn' : 5 ≤ n := by omega
  have hnR : (5:ℝ) ≤ n := by exact_mod_cast hn'
  have hb := angle_bounds hn
  have hlt : angle n < π/2 := by
    apply (div_lt_iff₀ (by positivity : 0 < (n:ℝ))).2
    nlinarith [Real.pi_pos]
  have hpos := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le (by linarith [Real.pi_pos]) hlt
  rw [Real.cos_pi_div_two] at hpos
  have hone := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ) ≤ 0) hb.2.le hb.1
  rw [Real.cos_zero] at hone
  have hji : 0 < j ∧ j < 2 := by
    constructor
    · exact_mod_cast (by linarith : (0:ℝ) < j)
    · exact_mod_cast (by linarith : (j:ℝ) < 2)
  have jone : j = 1 := by omega
  rw [jone, Int.cast_one] at he
  have eq : angle n = π/3 := Real.strictAntiOn_cos.injOn
    ⟨hb.1.le,hb.2.le⟩ ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
    (by rw [Real.cos_pi_div_three]; linarith)
  have eq' := (div_eq_iff (by positivity : (n:ℝ) ≠ 0)).1 eq
  have six : (n:ℝ) = 6 := by
    apply (mul_right_cancel₀ (ne_of_gt Real.pi_pos))
    linarith
  exact h.2.2 (by exact_mod_cast six)

end Shannon
