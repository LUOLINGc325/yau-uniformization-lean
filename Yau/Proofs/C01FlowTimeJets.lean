import Yau.Proofs.C01JointDirections

/-! Positive-time Ricci regularity and Hermitian time jets are consequences
of the actual smooth metric family and its original Kähler--Ricci equation.
No curvature estimate or completeness assumption is added. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_gMat_time_contDiffOn
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun t => gMat (h t) x i j) (Set.Ici 0) := by
  exact (Alignment.Y03Proof.metricFamily_hMat_contDiffOn hflow.1.2.1 x i j).comp
    (contDiffOn_const.prodMk contDiffOn_id)
    (fun t ht => ⟨mem_extChartAt_target (I := ComplexModel n) x, ht⟩)

theorem localizedFlow_gMat_hasDerivAt
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t)
    (i j : Fin n) :
    HasDerivAt (fun s => gMat (h s) x i j) (-(ricci (h t) x i j)) t :=
  (hflow.1.2.2.2 x t ht.le i j).hasDerivAt (Ici_mem_nhds ht)

theorem localizedFlow_ricci_time_contDiffOn
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun t => ricci (h t) x i j) (Set.Ioi 0) := by
  have hmetric : ContDiffOn ℝ ∞ (fun t => gMat (h t) x i j) (Set.Ioi 0) :=
    (localizedFlow_gMat_time_contDiffOn hflow x i j).mono Set.Ioi_subset_Ici_self
  have hderiv : ContDiffOn ℝ ∞ (deriv (fun t => gMat (h t) x i j)) (Set.Ioi 0) :=
    hmetric.deriv_of_isOpen isOpen_Ioi (by simp)
  apply hderiv.neg.congr
  intro t ht
  rw [(localizedFlow_gMat_hasDerivAt hflow x ht i j).deriv]
  simp

theorem localizedFlow_ricci_hasDerivAt
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t)
    (i j : Fin n) :
    HasDerivAt (fun s => ricci (h s) x i j)
      (deriv (fun s => ricci (h s) x i j) t) t :=
  ((localizedFlow_ricci_time_contDiffOn hflow x i j).contDiffAt
    (isOpen_Ioi.mem_nhds ht)).differentiableAt (by simp) |>.hasDerivAt

theorem localizedFlow_ricci_isHermitian
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t) :
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
  have hd := (localizedFlow_gMat_hasDerivAt hflow x ht j i).star
  rw [heq] at hd
  have hu := hd.unique (localizedFlow_gMat_hasDerivAt hflow x ht i j)
  simpa only [star_neg, neg_inj] using hu

theorem localizedFlow_ricci_timeDerivative_isHermitian
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    (Matrix.of (fun i j => deriv (fun s => ricci (h s) x i j) t)).IsHermitian := by
  ext i j
  change star (deriv (fun s => ricci (h s) x j i) t) =
    deriv (fun s => ricci (h s) x i j) t
  have heq : (fun s => star (ricci (h s) x j i)) =ᶠ[𝓝 t]
      (fun s => ricci (h s) x i j) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact congrArg (fun A : Herm n => A i j) (localizedFlow_ricci_isHermitian hflow x hs).eq
  have hd := (localizedFlow_ricci_hasDerivAt hflow x ht j i).star
  have hnew := hd.congr_of_eventuallyEq heq.symm
  exact hnew.unique (localizedFlow_ricci_hasDerivAt hflow x ht i j)

end Yau.NodeProofs.C01Aux
