import Yau.Proofs.D06HardyFourier

/-! Fourier Hilbert-basis uniqueness for actual L² functions, including the
constant identity coefficient calculation. -/

open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

theorem hardy_fourierCoeff_const (c : ℂ) (n : ℤ) :
    fourierCoeff (fun _ : HardyCircle => c) n = if n = 0 then c else 0 := by
  have heq : (fun _ : HardyCircle => c) = fun t => c * fourier 0 t := by
    funext t
    rw [fourier_zero, mul_one]
  rw [heq, fourierCoeff.const_mul]
  have h := congrFun (fourierCoeff_fourier (T := 2 * Real.pi) 0) n
  rw [h]
  by_cases hn : n = 0 <;> simp [Pi.single_apply, hn, eq_comm]

theorem hardy_fourierCoeff_unique (f g : HardyCircle → ℂ)
    (hf : MemLp f 2 hardyCircleMeasure) (hg : MemLp g 2 hardyCircleMeasure)
    (hcoeff : ∀ n : ℤ, fourierCoeff f n = fourierCoeff g n) :
    f =ᵐ[hardyCircleMeasure] g := by
  let F := hf.toLp f
  let G := hg.toLp g
  have hFG : F = G := by
    apply (fourierBasis (T := 2 * Real.pi)).repr.injective
    ext n
    rw [fourierBasis_repr, fourierBasis_repr,
      fourierCoeff_congr_ae hf.coeFn_toLp, fourierCoeff_congr_ae hg.coeFn_toLp]
    exact hcoeff n
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with t hft hgt
  rw [← hft, ← hgt]
  exact congrArg (fun a : Lp ℂ 2 hardyCircleMeasure => a t) hFG

end Yau.NodeProofs.D06Aux
