import Yau.Proofs.V03Fourier
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! The project's Fourier seminorm as an actual Hilbert norm of weighted
coefficients. This gives the seminorm triangle and Cauchy--Schwarz estimates. -/

open scoped Topology ComplexConjugate lp
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

def dirichletCoeff (u : ℝ → ℂ) (k : ℤ) : ℂ :=
  (Real.sqrt |(k : ℝ)| : ℂ) * circleFourier u k

theorem dirichletCoeff_norm_sq (u : ℝ → ℂ) (k : ℤ) :
    ‖dirichletCoeff u k‖ ^ 2 = |(k : ℝ)| * ‖circleFourier u k‖ ^ 2 := by
  rw [dirichletCoeff, norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (abs_nonneg _)]

theorem boundaryDSq_singleton_eq (u : ℝ → ℂ) :
    boundaryDSq (fun θ (_ : Unit) => u θ) =
      ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| * ‖circleFourier u k‖ ^ 2) := by
  simp [boundaryDSq, Int.cast_abs]

theorem dirichletCoeff_mem_iff (u : ℝ → ℂ) :
    Memℓp (dirichletCoeff u) 2 ↔ boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤ := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, dirichletCoeff_norm_sq]
  rw [boundaryDSq_singleton_eq]
  constructor
  · exact Summable.tsum_ofReal_ne_top
  · intro hu
    exact (ENNReal.summable_toReal hu).congr (fun k =>
      ENNReal.toReal_ofReal (mul_nonneg (abs_nonneg _) (sq_nonneg _)))

def dirichletVector (u : ℝ → ℂ)
    (hu : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤) : ℓ²(ℤ, ℂ) :=
  ⟨dirichletCoeff u, (dirichletCoeff_mem_iff u).mpr hu⟩

theorem dirichletVector_norm_sq (u : ℝ → ℂ)
    (hu : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤) :
    ‖dirichletVector u hu‖ ^ 2 = (boundaryDSq (fun θ (_ : Unit) => u θ)).toReal := by
  have hn := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (dirichletVector u hu)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
  rw [hn, boundaryDSq_singleton_eq, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro k
  exact (dirichletCoeff_norm_sq u k).trans (ENNReal.toReal_ofReal (by positivity)).symm

theorem dirichletVector_norm (u : ℝ → ℂ)
    (hu : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤) :
    ‖dirichletVector u hu‖ = Real.sqrt (boundaryDSq (fun θ (_ : Unit) => u θ)).toReal := by
  rw [← dirichletVector_norm_sq u hu, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem boundaryDSq_add_ne_top {u v : ℝ → ℂ}
    (hu : Continuous u) (hv : Continuous v)
    (huf : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤)
    (hvf : boundaryDSq (fun θ (_ : Unit) => v θ) ≠ ⊤) :
    boundaryDSq (fun θ (_ : Unit) => u θ + v θ) ≠ ⊤ := by
  apply (dirichletCoeff_mem_iff _).mp
  have hm := ((dirichletCoeff_mem_iff u).mpr huf).add
    ((dirichletCoeff_mem_iff v).mpr hvf)
  convert hm using 1
  funext k
  dsimp only [dirichletCoeff, Pi.add_apply]
  rw [circleFourier_add hu hv, mul_add]

theorem dirichletVector_add {u v : ℝ → ℂ} (hu : Continuous u) (hv : Continuous v)
    (huf : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤)
    (hvf : boundaryDSq (fun θ (_ : Unit) => v θ) ≠ ⊤)
    (hs : boundaryDSq (fun θ (_ : Unit) => u θ + v θ) ≠ ⊤) :
    dirichletVector (fun θ => u θ + v θ) hs =
      dirichletVector u huf + dirichletVector v hvf := by
  apply Subtype.ext
  funext k
  change dirichletCoeff (fun θ => u θ + v θ) k = dirichletCoeff u k + dirichletCoeff v k
  rw [dirichletCoeff, circleFourier_add hu hv]
  exact mul_add _ _ _

theorem boundaryDSq_sqrt_add_le {u v : ℝ → ℂ} (hu : Continuous u) (hv : Continuous v)
    (huf : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤)
    (hvf : boundaryDSq (fun θ (_ : Unit) => v θ) ≠ ⊤) :
    Real.sqrt (boundaryDSq (fun θ (_ : Unit) => u θ + v θ)).toReal ≤
      Real.sqrt (boundaryDSq (fun θ (_ : Unit) => u θ)).toReal +
      Real.sqrt (boundaryDSq (fun θ (_ : Unit) => v θ)).toReal := by
  have hs := boundaryDSq_add_ne_top hu hv huf hvf
  rw [← dirichletVector_norm _ hs, dirichletVector_add hu hv huf hvf hs,
    ← dirichletVector_norm u huf, ← dirichletVector_norm v hvf]
  exact norm_add_le _ _

def dirichletPair (u v : ℝ → ℂ) : ℂ :=
  ∑' k : ℤ, Complex.ofReal |(k : ℝ)| * circleFourier u k * star (circleFourier v k)

theorem dirichletPair_eq_inner (u v : ℝ → ℂ)
    (hu : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤)
    (hv : boundaryDSq (fun θ (_ : Unit) => v θ) ≠ ⊤) :
    dirichletPair u v = inner ℂ (dirichletVector v hv) (dirichletVector u hu) := by
  change (∑' k : ℤ, Complex.ofReal |(k : ℝ)| * circleFourier u k * star (circleFourier v k)) =
    ∑' k : ℤ, inner ℂ (dirichletCoeff v k) (dirichletCoeff u k)
  apply tsum_congr
  intro k
  have hs : ((Real.sqrt |(k : ℝ)| : ℂ)) ^ 2 = Complex.ofReal |(k : ℝ)| := by
    exact_mod_cast Real.sq_sqrt (abs_nonneg (k : ℝ))
  simp only [dirichletCoeff, RCLike.inner_apply, star_mul', Complex.star_def,
    map_mul, Complex.conj_ofReal]
  rw [← hs]
  ring

theorem dirichletPair_norm_le (u v : ℝ → ℂ)
    (hu : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤)
    (hv : boundaryDSq (fun θ (_ : Unit) => v θ) ≠ ⊤) :
    ‖dirichletPair u v‖ ≤
      Real.sqrt (boundaryDSq (fun θ (_ : Unit) => u θ)).toReal *
      Real.sqrt (boundaryDSq (fun θ (_ : Unit) => v θ)).toReal := by
  rw [dirichletPair_eq_inner u v hu hv]
  simpa only [dirichletVector_norm, mul_comm] using
    (norm_inner_le_norm (𝕜 := ℂ) (dirichletVector v hv) (dirichletVector u hu))

end Yau.Blueprint.V03Proof
