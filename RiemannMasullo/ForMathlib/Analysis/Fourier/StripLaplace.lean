module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # The two-sided Laplace transform on a vertical strip

For `f` square integrable against `exp (2 * α * |x|)`, the integral `∫ f x * exp (z * x)`
converges absolutely on the open strip `|re z| < α`, and its restriction to each vertical line
of the strip satisfies Plancherel's identity.
-/

open MeasureTheory Complex Metric
open scoped FourierTransform Real

@[expose] public noncomputable section

namespace RiemannMasullo

variable {f : ℝ → ℂ} {α : ℝ}

/-- The two-sided Laplace transform `z ↦ ∫ f x * exp (z * x)`. -/
def bilateralLaplace (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ x : ℝ, f x * cexp (z * x)

/-- A function is almost everywhere strongly measurable when its product with the weight
`exp (α * |x|)` is. -/
theorem aestronglyMeasurable_of_exp_abs_smul
    (hf : AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (α * |x|) • f x)) :
    AEStronglyMeasurable f := by
  have hc : Continuous fun x : ℝ ↦ Real.exp (-(α * |x|)) := by fun_prop
  refine (hc.aestronglyMeasurable.smul hf).congr (.of_forall fun x ↦ ?_)
  change Real.exp (-(α * |x|)) • (Real.exp (α * |x|) • f x) = f x
  rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

/-- The exponential `exp (-(c * |x|))` is integrable on the line for `c > 0`. -/
theorem integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable fun x : ℝ ↦ Real.exp (-(c * |x|)) := by
  have h := (integrable_inv_one_add_sq.comp_mul_left' hc.ne').const_mul 2
  refine h.mono' (by fun_prop) (.of_forall fun x ↦ ?_)
  have hu : 0 ≤ c * |x| := by positivity
  have h1 : 1 + (c * x) ^ 2 ≤ 2 * Real.exp (c * |x|) := by
    have := Real.quadratic_le_exp_of_nonneg hu
    have hsq : (c * x) ^ 2 = (c * |x|) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
    nlinarith [Real.add_one_le_exp (c * |x|)]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_neg, ← div_eq_mul_inv,
    inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  linarith

/-- On the open strip `|re z| < α`, the integrand of the two-sided Laplace transform of a
function in the weighted `L²` space is integrable. -/
theorem integrable_mul_cexp_of_memLp_exp_abs
    (hf : MemLp (fun x : ℝ ↦ Real.exp (α * |x|) • f x) 2) {z : ℂ} (hz : |z.re| < α) :
    Integrable fun x : ℝ ↦ f x * cexp (z * x) := by
  have hfm := aestronglyMeasurable_of_exp_abs_smul hf.aestronglyMeasurable
  have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hc : 0 < α - |z.re| := sub_pos.mpr hz
  have hexp := integrable_exp_neg_mul_abs (mul_pos two_pos hc)
  refine (hsq.add hexp).mono' (hfm.mul (by fun_prop)) (.of_forall fun x ↦ ?_)
  have hre : (z * x).re = z.re * x := by simp
  rw [norm_mul, Complex.norm_exp, hre]
  simp only [Pi.add_apply]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hx : z.re * x ≤ |z.re| * |x| := (le_abs_self _).trans (abs_mul _ _).le
  have hle : Real.exp (z.re * x) ≤ Real.exp (α * |x|) * Real.exp (-((α - |z.re|) * |x|)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hE : Real.exp (-(2 * (α - |z.re|) * |x|)) = Real.exp (-((α - |z.re|) * |x|)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hn := norm_nonneg (f x)
  calc ‖f x‖ * Real.exp (z.re * x)
      ≤ (Real.exp (α * |x|) * ‖f x‖) * Real.exp (-((α - |z.re|) * |x|)) := by
        nlinarith [mul_le_mul_of_nonneg_left hle hn]
    _ ≤ (Real.exp (α * |x|) * ‖f x‖) ^ 2 + Real.exp (-(2 * (α - |z.re|) * |x|)) := by
        rw [hE]
        nlinarith [sq_nonneg (Real.exp (α * |x|) * ‖f x‖ - Real.exp (-((α - |z.re|) * |x|))),
          sq_nonneg (Real.exp (α * |x|) * ‖f x‖), sq_nonneg (Real.exp (-((α - |z.re|) * |x|))),
          mul_nonneg (mul_nonneg (Real.exp_pos (α * |x|)).le hn)
            (Real.exp_pos (-((α - |z.re|) * |x|))).le]

/-- On the closed strip `|σ| ≤ α`, the damped function `f x * exp (σ * x)` is square
integrable. -/
theorem memLp_mul_exp_of_memLp_exp_abs
    (hf : MemLp (fun x : ℝ ↦ Real.exp (α * |x|) • f x) 2) {σ : ℝ} (hσ : |σ| ≤ α) :
    MemLp (fun x : ℝ ↦ f x * (Real.exp (σ * x) : ℂ)) 2 := by
  have hfm := aestronglyMeasurable_of_exp_abs_smul hf.aestronglyMeasurable
  refine hf.mono (hfm.mul (by fun_prop)) (.of_forall fun x ↦ ?_)
  rw [norm_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), mul_comm]
  have hx : σ * x ≤ α * |x| :=
    ((le_abs_self _).trans (abs_mul _ _).le).trans (mul_le_mul_of_nonneg_right hσ (abs_nonneg x))
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hx) (norm_nonneg _)

/-- Pointwise bound for the derivative of the integrand of the two-sided Laplace transform, at
distance at least `c` from the boundary of the strip. -/
private theorem hasDerivAt_bilateralLaplace_bound {c β : ℝ} (hc : 0 < c) (r x : ℝ) (n : ℝ)
    (hn : 0 ≤ n) (hr : |r| ≤ β) :
    n * (|x| * Real.exp (r * x)) ≤
      (Real.exp ((β + c) * |x|) * n) ^ 2 + 4 / c ^ 2 * Real.exp (-(c * |x|)) := by
  have hu : 0 ≤ |x| := abs_nonneg x
  have hrx : r * x ≤ β * |x| :=
    ((le_abs_self _).trans (abs_mul _ _).le).trans (mul_le_mul_of_nonneg_right hr hu)
  have hE : Real.exp (r * x) ≤ Real.exp ((β + c) * |x|) * Real.exp (-(c * |x|)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hsq : (c * |x| / 2) ^ 2 ≤ Real.exp (c * |x|) := by
    have h1 : c * |x| / 2 ≤ Real.exp (c * |x| / 2) := by
      linarith [Real.add_one_le_exp (c * |x| / 2)]
    have h2 : Real.exp (c * |x|) = Real.exp (c * |x| / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h2]
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hinv : Real.exp (-(c * |x|)) * Real.exp (c * |x|) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  set A := Real.exp ((β + c) * |x|) * n with hA
  set e := Real.exp (-(c * |x|)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hA0 : 0 ≤ A := mul_nonneg (Real.exp_pos _).le hn
  set B := |x| * e with hBdef
  have hB : B ^ 2 ≤ 4 / c ^ 2 * e := by
    have h3 : |x| ^ 2 * e ≤ 4 / c ^ 2 := by
      have h4 : |x| ^ 2 ≤ 4 / c ^ 2 * Real.exp (c * |x|) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
      calc |x| ^ 2 * e ≤ 4 / c ^ 2 * Real.exp (c * |x|) * e :=
            mul_le_mul_of_nonneg_right h4 he0.le
        _ = 4 / c ^ 2 := by rw [mul_assoc, mul_comm (Real.exp _) e, hinv, mul_one]
    calc B ^ 2 = |x| ^ 2 * e * e := by rw [hBdef]; ring
      _ ≤ 4 / c ^ 2 * e := mul_le_mul_of_nonneg_right h3 he0.le
  have hAB : A * B ≤ A ^ 2 + B ^ 2 := by
    nlinarith [sq_nonneg (A - B), sq_nonneg A, sq_nonneg B]
  calc n * (|x| * Real.exp (r * x)) ≤ n * (|x| * (Real.exp ((β + c) * |x|) * e)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE hu) hn
    _ = A * B := by rw [hA, hBdef]; ring
    _ ≤ A ^ 2 + 4 / c ^ 2 * e := by linarith

/-- On the open strip `|re z| < α`, the two-sided Laplace transform of a function in the
weighted `L²` space is complex differentiable, with derivative `∫ f x * (x * exp (z * x))`. -/
theorem hasDerivAt_bilateralLaplace
    (hf : MemLp (fun x : ℝ ↦ Real.exp (α * |x|) • f x) 2) {z : ℂ} (hz : |z.re| < α) :
    HasDerivAt (bilateralLaplace f) (∫ x : ℝ, f x * (x * cexp (z * x))) z := by
  have hfm := aestronglyMeasurable_of_exp_abs_smul hf.aestronglyMeasurable
  have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  set c := (α - |z.re|) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hbd : Integrable fun x : ℝ ↦
      ‖Real.exp (α * |x|) • f x‖ ^ 2 + 4 / c ^ 2 * Real.exp (-(c * |x|)) :=
    hsq.add ((integrable_exp_neg_mul_abs hc0).const_mul _)
  have hm1 (w : ℂ) : AEStronglyMeasurable fun x : ℝ ↦ f x * cexp (w * x) :=
    hfm.mul (by fun_prop : Continuous fun x : ℝ ↦ cexp (w * x)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable fun x : ℝ ↦ f x * (x * cexp (z * x)) :=
    hfm.mul (by fun_prop : Continuous fun x : ℝ ↦ (x : ℂ) * cexp (z * x)).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (x : ℝ) ↦ f x * cexp (w * x))
    (F' := fun (w : ℂ) (x : ℝ) ↦ f x * (x * cexp (w * x))) (ball_mem_nhds z hc0)
    (.of_forall hm1) (integrable_mul_cexp_of_memLp_exp_abs hf hz) hm2
    (.of_forall fun x w hw ↦ ?_) hbd (.of_forall fun x w _ ↦ ?_)).2
  · have hw' : |w.re| ≤ α - 2 * c + c := by
      have h1 : |w.re - z.re| ≤ ‖w - z‖ := by simpa using Complex.abs_re_le_norm (w - z)
      have h2 : ‖w - z‖ < c := by simpa [dist_eq_norm] using hw
      have h3 : |w.re| ≤ |z.re| + |w.re - z.re| := by
        simpa using abs_add_le z.re (w.re - z.re)
      rw [hc] at h2 ⊢
      linarith
    have hre : (w * x).re = w.re * x := by simp
    have := hasDerivAt_bilateralLaplace_bound hc0 w.re x ‖f x‖ (norm_nonneg _) hw'
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre,
      norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hα : α - 2 * c + c + c = α := by ring
    rwa [hα] at this
  · have h := (((hasDerivAt_id w).mul_const (x : ℂ)).cexp).const_mul (f x)
    simpa [mul_comm] using h

/-- The two-sided Laplace transform of a function in the weighted `L²` space is holomorphic on
the open strip `|re z| < α`. -/
theorem differentiableOn_bilateralLaplace
    (hf : MemLp (fun x : ℝ ↦ Real.exp (α * |x|) • f x) 2) :
    DifferentiableOn ℂ (bilateralLaplace f) {z : ℂ | |z.re| < α} := fun _ hz ↦
  (hasDerivAt_bilateralLaplace hf hz).differentiableAt.differentiableWithinAt

/-- Plancherel's identity on a vertical line of the open strip: the two-sided Laplace transform
of a function in the weighted `L²` space is square integrable on the line `re z = σ`, with
norm given by the weight `exp (2 * σ * x)`. -/
theorem integral_norm_sq_bilateralLaplace
    (hf : MemLp (fun x : ℝ ↦ Real.exp (α * |x|) • f x) 2) {σ : ℝ} (hσ : |σ| < α) :
    ∫ t : ℝ, ‖bilateralLaplace f (σ + t * I)‖ ^ 2 =
      2 * π * ∫ x : ℝ, ‖f x‖ ^ 2 * Real.exp (2 * σ * x) := by
  set g : ℝ → ℂ := fun x ↦ f x * (Real.exp (σ * x) : ℂ) with hg
  have hg2 : MemLp g 2 := memLp_mul_exp_of_memLp_exp_abs hf hσ.le
  have hg1 : Integrable g := by
    have h := integrable_mul_cexp_of_memLp_exp_abs hf (z := (σ : ℂ)) (by simpa using hσ)
    refine h.congr (.of_forall fun x ↦ ?_)
    simp only [hg, Complex.ofReal_exp, Complex.ofReal_mul]
  obtain ⟨hF2, hnorm⟩ := memLp_two_fourier_and_eLpNorm_eq hg1 hg2
  have h0 (h : ℝ → ℂ) : 0 ≤ ∫ x, ‖h x‖ ^ 2 := integral_nonneg fun _ ↦ by positivity
  have key : ∫ ξ, ‖𝓕 g ξ‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 := by
    rw [hF2.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      hg2.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top] at hnorm
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hnorm
    have h1 := (ENNReal.ofReal_eq_ofReal_iff (Real.rpow_nonneg (h0 _) _)
      (Real.rpow_nonneg (h0 _) _)).mp hnorm
    have h2 := congrArg (· ^ (2 : ℝ)) h1
    simpa only [Real.rpow_inv_rpow (h0 _) two_ne_zero] using h2
  have hL (t : ℝ) : bilateralLaplace f (σ + t * I) = 𝓕 g (t / (-(2 * π))) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    unfold bilateralLaplace
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    have hph : ((-2 * π * x * (t / (-(2 * π))) : ℝ) : ℂ) = t * x := by
      have := Real.pi_ne_zero
      push_cast
      field_simp
    simp only [hg, smul_eq_mul]
    rw [hph, Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  calc ∫ t : ℝ, ‖bilateralLaplace f (σ + t * I)‖ ^ 2
      = ∫ t : ℝ, (fun ξ ↦ ‖𝓕 g ξ‖ ^ 2) (t / (-(2 * π))) := by simp only [hL]
    _ = |-(2 * π)| • ∫ ξ, ‖𝓕 g ξ‖ ^ 2 := by
        convert Measure.integral_comp_div (fun ξ : ℝ ↦ ‖𝓕 g ξ‖ ^ 2) (-(2 * π)) using 1
    _ = 2 * π * ∫ x, ‖g x‖ ^ 2 := by
        rw [key, abs_neg, abs_of_pos (by positivity), smul_eq_mul]
    _ = 2 * π * ∫ x : ℝ, ‖f x‖ ^ 2 * Real.exp (2 * σ * x) := by
        congr 1
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        simp only [hg]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
          ← Real.exp_nat_mul]
        congr 2
        push_cast
        ring

end RiemannMasullo
