import Yau.Proofs.D06WeightedCore
import Yau.Proofs.D06HardyPure

/-! The unilateral shift preserves the actual weighted Hardy inner product. -/

open scoped ComplexOrder
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardyWeightedInner_shift (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (a b : HardySeq r) :
    hardyWeightedInner L (hardyShift a) (hardyShift b) = hardyWeightedInner L a b := by
  unfold hardyWeightedInner
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [hardyTrace_shift_ae a i, hardyTrace_shift_ae b j] with t ha hb
  rw [ha, hb, star_mul]
  have hn : ‖fourier 1 t‖ = 1 := by simp only [fourier_apply, Circle.norm_coe]
  have hχ : star (fourier 1 t) * fourier 1 t = 1 := by
    simpa only [← RCLike.star_def, hn, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_one, one_pow] using RCLike.conj_mul (fourier 1 t)
  calc
    _ = (star (fourier 1 t) * fourier 1 t) *
        (star (hardyTraceLp a i t) * L t i j * hardyTraceLp b j t) := by ring
    _ = _ := by rw [hχ, one_mul]

def weightedShiftLinear : WeightedHardySeq r →ₗ[ℂ] WeightedHardySeq r :=
  weightedWrapLM.comp ((hardyShiftLI : HardySeq r →ₗᵢ[ℂ] HardySeq r).toLinearMap.comp weightedUnwrapLM)

theorem weightedShiftLinear_unwrap (a : WeightedHardySeq r) :
    weightedUnwrap (weightedShiftLinear a) = hardyShift (weightedUnwrap a) := rfl

theorem weightedShiftLinear_pow_unwrap (k : ℕ) (a : WeightedHardySeq r) :
    weightedUnwrap ((weightedShiftLinear ^ k) a) =
      ((hardyShiftLI : HardySeq r →ₗᵢ[ℂ] HardySeq r) ^ k) (weightedUnwrap a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', pow_succ']
      change weightedUnwrap (weightedShiftLinear ((weightedShiftLinear ^ k) a)) =
        hardyShift ((hardyShiftLI ^ k) (weightedUnwrap a))
      rw [weightedShiftLinear_unwrap, ih]

theorem weightedShiftLinear_pure :
    (⨅ k : ℕ, (weightedShiftLinear (r := r) ^ k).range) = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro a ha
  apply weightedUnwrap.injective
  change weightedUnwrap a = 0
  have hall : weightedUnwrap a ∈
      ⨅ k : ℕ, ((hardyShiftLI : HardySeq r →ₗᵢ[ℂ] HardySeq r) ^ k).range := by
    apply (Submodule.mem_iInf _).mpr
    intro k
    obtain ⟨b, hb⟩ := (Submodule.mem_iInf _).mp ha k
    refine ⟨weightedUnwrap b, ?_⟩
    exact (weightedShiftLinear_pow_unwrap k b).symm.trans (congrArg weightedUnwrap hb)
  rwa [hardyShift_pure, Submodule.mem_bot] at hall

variable (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
variable (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
variable (hHerm : ∀ t, (L t).IsHermitian)
variable (m : ℝ) (hm : 0 < m)
variable (hLower : ∀ t, (L t - (m : ℂ) • 1).PosSemidef)

def weightedShiftLI :
    letI : NormedAddCommGroup (WeightedHardySeq r) :=
      weightedHardyNormed L hLp hHerm m hm hLower
    WeightedHardySeq r →ₗᵢ[ℂ] WeightedHardySeq r := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  refine { weightedShiftLinear with norm_map' := ?_ }
  intro a
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [weightedHardy_norm_sq L hLp hHerm m hm hLower,
    weightedHardy_norm_sq L hLp hHerm m hm hLower, weightedShiftLinear_unwrap]
  exact congrArg Complex.re (hardyWeightedInner_shift L (weightedUnwrap a) (weightedUnwrap a))

end Yau.NodeProofs.D06Aux
