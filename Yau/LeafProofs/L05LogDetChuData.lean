import Yau.LeafProofs.L05LogDetConcavity

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

local instance l05LogDetChuDataSymContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Sym n) :=
  (show Topology.IsInducing (fun A : Sym n => (A : Mat n)) from ⟨rfl⟩).continuousSMul
    (f := fun c : ℝ => c) continuous_id (by intros; rfl)

theorem logDetReal_chuH1 {n : ℕ} {ell L K beta : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) (hK : 0 ≤ K)
    (hb : ∀ A ∈ slopeSet n ell L, |logDetReal A| ≤ K) :
    ChuH1 (slopeSet n ell L) (logDetDomain n) (fun A _ => logDetReal A)
      ((1/2:ℝ)*L⁻¹) ((1/2:ℝ)*ell⁻¹) K beta := by
  refine ⟨logDetDomain_isOpen n,slopeSet_subset_logDetDomain hell,?_,?_,?_,?_,hb⟩
  · exact (logDetReal_contDiffOn n).of_le (by simp) |>.comp contDiff_fst.contDiffOn (fun _ hz => hz.1)
  · intro A hA p hp v
    exact logDetReal_rankOne_elliptic hell hL hA v
  · intro A hA B hB p hp
    have hh := (logDetReal_concaveOn_slopeSet hell hL).2 hA hB
      (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
      (show (1/2:ℝ)+1/2=1 by norm_num)
    have hmat : (1/2:ℝ) • A+(1/2:ℝ) • B=(1/2:ℝ) • (A+B) := (smul_add _ _ _).symm
    rw [hmat] at hh
    change (1/2:ℝ)*logDetReal A+(1/2:ℝ)*logDetReal B ≤ _ at hh
    linarith only [hh]
  · intro A hA p hp q hq
    rw [sub_self,abs_zero]
    apply mul_nonneg hK
    exact add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)

theorem logDetReal_chuData {n : ℕ} {ell L K beta : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) (hK : 0 < K) :
    ∃ Kstar : ℝ, 0 < Kstar ∧ K ≤ Kstar ∧ (1/2:ℝ) ≤ Kstar ∧
      2*Real.sqrt (2*n) ≤ Kstar ∧
      ChuH1 (slopeSet n ell L) (logDetDomain n) (fun A _ => logDetReal A)
        ((1/2:ℝ)*L⁻¹) ((1/2:ℝ)*ell⁻¹) Kstar beta ∧
      ChuH2 (fun A (_ : Point n) => complexHessianMap A) Kstar beta ∧
      Modulus (fun r => logDetDerivativeConstant n ell*r) ∧
      ChuDerivativeModulus (slopeSet n ell L) (fun A _ => logDetReal A)
        (fun r => logDetDerivativeConstant n ell*r) := by
  have hct := slopeSet_isCompact n hell.le (L := L)
  have hc : ContinuousOn (fun A : Sym n => |logDetReal A|) (slopeSet n ell L) :=
    ((logDetReal_contDiffOn n).continuousOn.mono (slopeSet_subset_logDetDomain hell)).abs
  obtain ⟨M,hM⟩ := hct.bddAbove_image hc
  let Kstar := 1+K+2*Real.sqrt (2*n)+|M|
  have hpos : 0 < Kstar := by dsimp only [Kstar]; positivity
  have hKstar : K ≤ Kstar := by
    dsimp only [Kstar]
    linarith only [Real.sqrt_nonneg (2*n),abs_nonneg M]
  have hhalf : (1/2:ℝ) ≤ Kstar := by
    dsimp only [Kstar]
    linarith only [hK,Real.sqrt_nonneg (2*n),abs_nonneg M]
  have hdim : 2*Real.sqrt (2*n) ≤ Kstar := by
    dsimp only [Kstar]
    linarith only [hK,abs_nonneg M]
  have hb : ∀ A ∈ slopeSet n ell L, |logDetReal A| ≤ Kstar := by
    intro A hA
    have hh := hM (Set.mem_image_of_mem (fun A : Sym n => |logDetReal A|) hA)
    have hMabs := le_abs_self M
    dsimp only [Kstar]
    linarith only [hh,hMabs,hK,Real.sqrt_nonneg (2*n)]
  exact ⟨Kstar,hpos,hKstar,hhalf,hdim,logDetReal_chuH1 hell hL hpos.le hb,
    complexHessianMap_chuH2 hpos hhalf hdim,linearModulus (logDetDerivativeConstant_nonneg n ell),
    logDetReal_chuDerivativeModulus hell hL Set.Subset.rfl⟩

end Yau.LeafProofs.L05Aux
