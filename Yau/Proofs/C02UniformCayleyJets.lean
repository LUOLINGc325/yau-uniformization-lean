import Yau.Proofs.C02ComplexSumInverse
import Yau.Proofs.C02LocalInverseJetBounds
import Yau.Proofs.C02LocalConstantJetBounds

/-! Uniform jets of the actual Cayley expression, on the original fixed
smooth domain. All constants precede the complex-structure field. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ}
local instance cay_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance cay_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

def complexCayleyField (J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (x : ComplexVector n) : ComplexVector n →L[ℝ] ComplexVector n :=
  (J x + complexStructureCLM n).inverse.comp (complexStructureCLM n - J x)

theorem exists_uniform_cayley_jet_bounds (n : ℕ) (b : ℕ → ℝ) :
    ∃ c : ℕ → ℝ, (∀ m, 0 ≤ c m) ∧
      ∀ (O : Set (ComplexVector n)), IsOpen O →
      ∀ J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n,
      ContDiffOn ℝ ∞ J O →
      (∀ x ∈ O, ‖J x - complexStructureCLM n‖ ≤ 1 / 4) →
      (∀ m x, x ∈ O → ‖iteratedFDeriv ℝ m J x‖ ≤ b m) →
      ContDiffOn ℝ ∞ (complexCayleyField J) O ∧
      ∀ m x, x ∈ O → ‖iteratedFDeriv ℝ m (complexCayleyField J) x‖ ≤ c m := by
  let β := fun m => 1 + |b m|
  have hβ (m : ℕ) : 0 ≤ β m := by dsimp only [β]; positivity
  let c := binomialJetProduct (inverseJetMajorant β) β
  refine ⟨c, fun m => binomialJetProduct_nonneg (inverseJetMajorant_nonnegative hβ) hβ m, ?_⟩
  intro O hO J hJ hClose hBound
  let I := complexStructureCLM n
  let B := fun x => J x + I
  let D := fun x => I - J x
  let C := fun x => (B x).inverse
  have hB : ContDiffOn ℝ ∞ B O := hJ.add contDiffOn_const
  have hD : ContDiffOn ℝ ∞ D O := contDiffOn_const.sub hJ
  have hInv (x : ComplexVector n) (hx : x ∈ O) : (B x).IsInvertible :=
    (complex_sum_isInvertible_and_inverse_norm (J x) (hClose x hx)).1
  have hC : ContDiffOn ℝ ∞ C O := by
    intro x hx
    exact ((hInv x hx).contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞)).comp_contDiffWithinAt x (hB x hx)
  have hBc (m : ℕ) (x : ComplexVector n) (hx : x ∈ O) : ‖iteratedFDeriv ℝ m B x‖ ≤ β m := by
    have hh := norm_iteratedFDeriv_const_add_on_le hO hJ hx I m
    have heq : B = fun y => I + J y := funext (fun y => add_comm _ _)
    rw [heq]
    apply hh.trans
    split_ifs with hm
    · subst m
      have hb := hBound 0 x hx
      rw [norm_iteratedFDeriv_zero] at hb
      have hI := complexStructureCLM_norm_le_one n
      dsimp only [β]
      linarith [le_abs_self (b 0)]
    · exact (hBound m x hx).trans (by dsimp only [β]; linarith [le_abs_self (b m)])
  have hDc (m : ℕ) (x : ComplexVector n) (hx : x ∈ O) : ‖iteratedFDeriv ℝ m D x‖ ≤ β m := by
    apply (norm_iteratedFDeriv_const_sub_on_le hO hJ hx I m).trans
    split_ifs with hm
    · subst m
      have hb := hBound 0 x hx
      rw [norm_iteratedFDeriv_zero] at hb
      have hI := complexStructureCLM_norm_le_one n
      dsimp only [β]
      linarith [le_abs_self (b 0)]
    · exact (hBound m x hx).trans (by dsimp only [β]; linarith [le_abs_self (b m)])
  have hCc (m : ℕ) (x : ComplexVector n) (hx : x ∈ O) :
      ‖iteratedFDeriv ℝ m C x‖ ≤ inverseJetMajorant β m :=
    actualInverseField_jet_majorant_on hO hB hInv hx β hβ (fun i => hBc i x hx)
      ((complex_sum_isInvertible_and_inverse_norm (J x) (hClose x hx)).2.trans (by norm_num)) m
  refine ⟨hC.clm_comp hD, ?_⟩
  intro m x hx
  exact (norm_iteratedFDeriv_bilinearOn_le
    (ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) (ComplexVector n))
    (ContinuousLinearMap.norm_compL_le ℝ (ComplexVector n) (ComplexVector n) (ComplexVector n))
    hO hC hD hx m).trans (binomialJetProduct_mono m
      (fun i _ => hCc i x hx) (fun i _ => hDc i x hx)
      (fun i _ => norm_nonneg _) (fun i _ => hβ i))

end Yau.Blueprint.C02Proof
