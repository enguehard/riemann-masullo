module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The Cauchy kernel split by frequency

For `p` in the upper half-plane and real `x`, the Cauchy kernel `(x - p)⁻¹` is a superposition of
the oscillations `exp (-i (x - p) τ)` over `τ > 0`. Cutting the frequencies at `T` splits it
into a band-limited part `(1 - exp (-i T (x - p))) / (x - p)` and a remainder
`exp (-i T (x - p)) / (x - p)` carried by the frequencies above `T`. This is the formula for
the Paley–Wiener projection of a simple pole.
-/

open MeasureTheory Complex Set

@[expose] public noncomputable section

namespace RiemannMasullo

/-- The exponent `-i (x - p)` has negative real part when `p` is in the upper half-plane. -/
theorem re_neg_I_mul_sub_neg {p : ℂ} (hp : 0 < p.im) (x : ℝ) : (-I * ((x : ℂ) - p)).re < 0 := by
  simp
  exact hp

/-- The band-limited part of the Cauchy kernel: frequencies between `0` and `T`. -/
theorem integral_cexp_cauchyKernel_band {p : ℂ} (hp : 0 < p.im) (x T : ℝ) :
    ∫ τ in (0 : ℝ)..T, cexp (-I * ((x : ℂ) - p) * τ) =
      I * (cexp (-I * ((x : ℂ) - p) * T) - 1) / ((x : ℂ) - p) := by
  have hc : -I * ((x : ℂ) - p) ≠ 0 := fun h ↦ by
    have := re_neg_I_mul_sub_neg hp x
    rw [h] at this
    simp at this
  have hxp : (x : ℂ) - p ≠ 0 := fun h ↦ hc (by rw [h, mul_zero])
  rw [integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The remainder of the Cauchy kernel: frequencies above `T`. -/
theorem integral_cexp_cauchyKernel_tail {p : ℂ} (hp : 0 < p.im) (x T : ℝ) :
    ∫ τ in Ioi T, cexp (-I * ((x : ℂ) - p) * τ) =
      -I * cexp (-I * ((x : ℂ) - p) * T) / ((x : ℂ) - p) := by
  have hre := re_neg_I_mul_sub_neg hp x
  have hc : -I * ((x : ℂ) - p) ≠ 0 := fun h ↦ by rw [h] at hre; simp at hre
  have hxp : (x : ℂ) - p ≠ 0 := fun h ↦ hc (by rw [h, mul_zero])
  rw [integral_exp_mul_complex_Ioi hre T]
  field_simp
  ring_nf
  simp [Complex.I_sq]

/-- The Cauchy kernel is the sum of its band-limited part and its remainder. -/
theorem integral_cexp_cauchyKernel_band_add_tail {p : ℂ} (hp : 0 < p.im) (x T : ℝ) :
    (∫ τ in (0 : ℝ)..T, cexp (-I * ((x : ℂ) - p) * τ)) +
        ∫ τ in Ioi T, cexp (-I * ((x : ℂ) - p) * τ) = -I / ((x : ℂ) - p) := by
  rw [integral_cexp_cauchyKernel_band hp, integral_cexp_cauchyKernel_tail hp]
  ring

end RiemannMasullo
