import Yau.Proofs.C01RicciNonnegative
import Yau.Proofs.C01MetricQuadraticJets

/-! The original Kähler--Ricci equation and the proved Ricci sign compare
the same metric at any two nonnegative times, including the initial endpoint. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_metric_quadratic_antitoneOn
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) (v : Fin n → ℂ) :
    AntitoneOn (fun t => (star v ⬝ᵥ (gMat (h t) x *ᵥ v)).re) (Set.Ici 0) := by
  have hInt : interior (Set.Ici (0 : ℝ)) = Set.Ioi 0 := interior_Ici
  apply antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ))
    (localizedFlow_metric_quadratic_contDiffOn hflow x v).continuousOn
  · intro t ht
    rw [hInt] at ht
    exact (localizedFlow_metric_quadratic_hasDerivAt hflow x ht v).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [hInt] at ht
    rw [(localizedFlow_metric_quadratic_hasDerivAt hflow x ht v).deriv]
    apply neg_nonpos.mpr
    exact (Complex.nonneg_iff.mp
      ((localizedFlow_ricci_posSemidef_posTime hflow hjoint x ht).dotProduct_mulVec_nonneg v)).1

theorem localizedFlow_metric_monotonicity
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) (t t' : ℝ) (ht : 0 ≤ t) (htt' : t ≤ t') :
    HermLE (gMat (h t') x) (gMat (h t) x) := by
  have hherm (s : ℝ) : (gMat (h s) x).IsHermitian :=
    (Alignment.Y03Proof.hMat_posDef (h s) x (chartPt x x)
      (mem_extChartAt_target (I := ComplexModel n) x)).isHermitian
  have hdiff : (gMat (h t) x - gMat (h t') x).IsHermitian :=
    (hherm t).sub (hherm t')
  unfold HermLE
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hdiff
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hdiff.im_star_dotProduct_mulVec_self v).symm⟩
  have hp := localizedFlow_metric_quadratic_antitoneOn hflow hjoint x v ht (ht.trans htt') htt'
  simpa only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, sub_nonneg] using hp

end Yau.NodeProofs.C01Aux
