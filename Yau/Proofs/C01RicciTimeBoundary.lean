import Yau.Proofs.C01FlowTimeJets

/-! The same original Ricci coefficients are smooth from the right at
time zero, by differentiating the original one-sided metric evolution. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_ricci_time_contDiffOn_nonneg
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun t => ricci (h t) x i j) (Set.Ici 0) := by
  have hmetric := localizedFlow_gMat_time_contDiffOn hflow x i j
  have hd : ContDiffOn ℝ ∞
      (derivWithin (fun t => gMat (h t) x i j) (Set.Ici 0)) (Set.Ici 0) :=
    hmetric.derivWithin (uniqueDiffOn_Ici 0) (by simp)
  apply hd.neg.congr
  intro t ht
  rw [(hflow.1.2.2.2 x t ht i j).derivWithin (uniqueDiffOn_Ici 0 t ht)]
  simp

theorem localizedFlow_ricci_isHermitian_nonneg
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 ≤ t) :
    (ricci (h t) x).IsHermitian := by
  have hmetric (s : ℝ) : (gMat (h s) x).IsHermitian :=
    (Alignment.Y03Proof.hMat_posDef (h s) x (chartPt x x)
      (mem_extChartAt_target (I := ComplexModel n) x)).isHermitian
  ext i j
  change star (ricci (h t) x j i) = ricci (h t) x i j
  have heq : (fun s => star (gMat (h s) x j i)) =
      (fun s => gMat (h s) x i j) := by
    funext s
    exact congrArg (fun A : Herm n => A i j) (hmetric s).eq
  have hd := (hflow.1.2.2.2 x t ht j i).star
  rw [heq] at hd
  have hu := (hd.derivWithin (uniqueDiffOn_Ici 0 t ht)).symm.trans
    ((hflow.1.2.2.2 x t ht i j).derivWithin (uniqueDiffOn_Ici 0 t ht))
  simpa only [star_neg, neg_inj] using hu

end Yau.NodeProofs.C01Aux
