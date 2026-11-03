import Yau.Proofs.V04HeatLinearity
import Yau.Proofs.V03Walls

/-! The reciprocal base wall is differentiated only where the original
boundary condition makes it positive. No global smooth wall is assumed. -/

open scoped Manifold Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.HeatAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem baseCost_smoothSpaceTime {d : VariationData X q} (hd : VariationSetup d) (j : ℕ) :
    SmoothSpaceTime (baseCost d j) (Set.Icc 0 d.extendedT) := by
  intro x
  change ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ =>
    ((j + 1 : ℕ) : ℝ)⁻¹ * d.Q (chartInv x p.1) p.2 + d.rhoTail j (chartInv x p.1) p.2)
      (chartTarget x ×ˢ Set.Icc 0 d.extendedT)
  exact (contDiffOn_const.mul (hd.2.2.2.2.2.2.2.2.1.1 x)).add
    ((hd.2.2.2.2.2.2.2.2.2.1 j).1 x)

theorem wallBase_local_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : X.manifold.Carrier) (hx : d.u x < d.A j) :
    ContDiffAt ℝ ∞ (inChart x (wallBase d j)) (chartPt x x) := by
  have hp := setup_wallProfiles hd
  have hz := (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  have hopen := isOpen_extChartAt_target (I := ComplexModel n) x
  have hleft : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hdelta : ContDiffOn ℝ ∞ (inChart x (deltaBase d j)) (chartTarget x) := by
    change ContDiffOn ℝ ∞ (fun z => d.profileBase (d.u (chartInv x z) / d.A j)) (chartTarget x)
    exact hp.1.comp_contDiffOn ((hd.2.2.2.1.1 x).div_const (d.A j))
  have hδ : inChart x (deltaBase d j) (chartPt x x) ≠ 0 := by
    simpa only [inChart, hleft] using (deltaBase_pos hp (setup_index_bounds hd j).1 hx).ne'
  have hs := ((hdelta.contDiffAt (hopen.mem_nhds hz)).inv hδ).sub (contDiffAt_const (c := (1 : ℝ)))
  change ContDiffAt ℝ ∞ (fun z => (inChart x (deltaBase d j) z)⁻¹ - 1) (chartPt x x)
  exact hs

theorem laplacian_baseCost_add_wallBase {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : X.manifold.Carrier) {t : ℝ} (ht : t ∈ Set.Icc 0 d.T)
    (hx : d.u x < d.A j) (s : ℝ) :
    laplacian (d.h t) (fun y => baseCost d j y t + (1 + s) * wallBase d j y) x =
      laplacian (d.h t) (fun y => baseCost d j y t) x +
        (1 + s) * laplacian (d.h t) (wallBase d j) x := by
  have ht' : t ∈ Set.Icc 0 d.extendedT := ⟨ht.1, ht.2.trans hd.2.1.le⟩
  have hbase := smoothSpaceTime_slice (baseCost_smoothSpaceTime hd j) ht'
  have hz := (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  have hopen := isOpen_extChartAt_target (I := ComplexModel n) x
  have hb : ContDiffAt ℝ 2 (inChart x (fun y => baseCost d j y t)) (chartPt x x) :=
    ((hbase x).contDiffAt (hopen.mem_nhds hz)).of_le (by simp)
  have hw : ContDiffAt ℝ 2 (inChart x (wallBase d j)) (chartPt x x) :=
    (wallBase_local_contDiffAt hd j x hx).of_le (by simp)
  have hscaled : ContDiffAt ℝ 2 (inChart x (fun y => (1 + s) * wallBase d j y)) (chartPt x x) := by
    change ContDiffAt ℝ 2 (fun z => (1 + s) * inChart x (wallBase d j) z) (chartPt x x)
    exact contDiffAt_const.mul hw
  calc
    _ = laplacian (d.h t) (fun y => baseCost d j y t) x +
      laplacian (d.h t) (fun y => (1 + s) * wallBase d j y) x :=
        laplacian_add_at (d.h t) x hb hscaled
    _ = _ := by rw [laplacian_const_mul_at (d.h t) x hw (1 + s)]

end Yau.Blueprint.V04Proof.HeatAux
