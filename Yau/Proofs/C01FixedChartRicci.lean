import Yau.Proofs.C01RicciPositive
import Yau.Proofs.C01ChartDetRatio

/-! Ricci in one fixed spatial chart is the actual negative time
derivative of that chart's metric matrix.  This supplies spatial continuity
without assuming continuity of the arbitrarily recentered chart choice. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

def fixedChartRicciMatrix (h : Flow X) (x : Pt X) (z : ComplexVector n) (t : ℝ) : Herm n :=
  Matrix.of fun i j => -(deriv (fun s => hMat (h s) x z i j) t)

theorem localizedFlow_hMat_timeDerivative_contDiffOn
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) (t : ℝ) (ht : 0 < t) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => deriv (fun s => hMat (h s) x z i j) t) (chartTarget x) := by
  let F : ComplexVector n × ℝ → ℂ := fun p => hMat (h p.2) x p.1 i j
  let S : Set (ComplexVector n × ℝ) := chartTarget x ×ˢ Set.Ioi 0
  have hS : IsOpen S := (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi
  have hF : ContDiffOn ℝ ∞ F S :=
    (Yau.Blueprint.Alignment.Y03Proof.metricFamily_hMat_contDiffOn hflow.1.2.1 x i j).mono
      (fun p hp => ⟨hp.1, Set.Ioi_subset_Ici_self hp.2⟩)
  have hEval : ContDiffOn ℝ ∞ (fun p => fderiv ℝ F p (0, 1)) S :=
    (hF.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const
  apply (hEval.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)).congr
  intro z hz
  have hp : (z, t) ∈ S := ⟨hz, ht⟩
  have hFD := ((hF.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hγ : HasDerivAt (fun s : ℝ => (z, s)) ((0 : ComplexVector n), (1 : ℝ)) t := by
    simpa only [id_eq] using! (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
  have hd : HasDerivAt (fun s => hMat (h s) x z i j) (fderiv ℝ F (z, t) (0, 1)) t := by
    simpa only [Function.comp_def, F] using! hFD.comp_hasDerivAt t hγ
  exact hd.deriv

theorem localizedFlow_fixedChartRicci_contDiffOn
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) (t : ℝ) (ht : 0 < t) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => fixedChartRicciMatrix h x z t i j) (chartTarget x) :=
  (localizedFlow_hMat_timeDerivative_contDiffOn hflow x t ht i j).neg

theorem fixedChartRicciMatrix_center_congruence
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) (z : ComplexVector n) (t : ℝ) (ht : 0 < t) :
    fixedChartRicciMatrix h x z t =
      (centerFrameMatrix x (chartInv x z))ᴴ * ricci (h t) (chartInv x z) *
        centerFrameMatrix x (chartInv x z) := by
  let y := chartInv x z
  let J : Herm n := centerFrameMatrix x y
  change fixedChartRicciMatrix h x z t = Jᴴ * ricci (h t) y * J
  ext i j
  have hfun : (fun s => hMat (h s) x z i j) = (fun s => (Jᴴ * gMat (h s) y * J) i j) := by
    funext s
    exact congrArg (fun A : Herm n => A i j) (hMat_center_congruence (h s) x z)
  have hin (q : Fin n) := HasDerivAt.fun_sum (u := Finset.univ)
    (fun p _ => (localizedFlow_gMat_hasDerivAt hflow y ht p q).const_mul (star (J p i)))
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun q _ => (hin q).mul_const (J q j))
  have hd : HasDerivAt (fun s => hMat (h s) x z i j) (-((Jᴴ * ricci (h t) y * J) i j)) t := by
    rw [hfun]
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, neg_mul, mul_neg,
      Finset.sum_neg_distrib] using! hs
  change -(deriv (fun s => hMat (h s) x z i j) t) = _
  rw [hd.deriv, neg_neg]

theorem localizedFlow_fixedChartRicci_posDef
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) (z : ComplexVector n) (hz : z ∈ chartTarget x) (t : ℝ) (ht : 0 < t) :
    (fixedChartRicciMatrix h x z t).PosDef := by
  rw [fixedChartRicciMatrix_center_congruence hflow x z t ht]
  have hJ : IsUnit (centerFrameMatrix x (chartInv x z)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
      (centerFrameMatrix_det_ne_zero x z hz (h t)))
  exact (localizedFlow_ricci_posDef hflow hjoint t ht.le (chartInv x z)).conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit hJ)

end Yau.NodeProofs.C01Aux
