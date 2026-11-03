import Yau.Proofs.E03FixedGapRegularity

/-! Derivative and Levi identities for the actual fixed-chart cometric logarithm. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Set

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint
variable {n : ℕ} {X : KahlerManifold n}

theorem negative_logDet_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (x : Pt X) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => -logDet (h s) x (chartPt x x))
      (scalarCurvature (h t) x) t := by
  have hz : chartPt x x ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hr := (Yau.F04Proof.rho_hasDerivWithinAt o h U P ρ hloc x t ht.le).hasDerivAt
    (Ici_mem_nhds ht)
  apply (hr.sub_const (logDet X.metric.form x (chartPt x x))).congr_of_eventuallyEq
  filter_upwards [Ici_mem_nhds ht] with s hs
  have he := Yau.F04Proof.rho_in_fixed_chart o h U P ρ hloc x s hs (chartPt x x) hz
  rw [hx] at he
  linarith

theorem smoothNear_time_differentiableAt (φ : Pt X → ℝ → ℝ) (x : Pt X) (t : ℝ)
    (hφ : SmoothNear φ x t) : DifferentiableAt ℝ (φ x) t := by
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hc : ContDiffAt ℝ ∞ (fun s : ℝ => (chartPt x x, s)) t :=
    contDiffAt_const.prodMk contDiffAt_id
  have hh := hφ.comp t hc
  simpa only [Function.comp_def, hx] using hh.differentiableAt (by norm_num)

theorem leviC_zero (z : ComplexVector n) : leviC (fun _ : ComplexVector n => (0 : ℝ)) z = 0 := by
  ext i j
  simp [leviC, leviMatrix, wirt, wirtBar]

theorem test_difference_levi (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (x : Pt X) (t : ℝ) (ht : 0 ≤ t)
    (φ : Pt X → ℝ → ℝ) (hφ : SmoothNear φ x t) :
    leviC (fun z => -logDet (h t) x z - φ (chartInv x z) t) (chartPt x x) =
      ricci (h t) x - levi (fun y => φ y t) x := by
  have hz : chartPt x x ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  have hh := (Yau.F04Proof.logDet_contDiffOn_of_metricSmooth (h t)
    (Yau.F04Proof.metricFamilySmooth_slice h (Ici 0) hloc.1.2.1 t ht) x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)
  have hi : ContDiffAt ℝ ∞ (fun z : ComplexVector n => (z, t)) (chartPt x x) :=
    contDiffAt_id.prodMk contDiffAt_const
  have hs0 : ContDiffAt ℝ ∞ (fun p : ComplexVector n × ℝ => φ (chartInv x p.1) p.2)
      (chartPt x x, t) := hφ
  have hs : ContDiffAt ℝ ∞ (fun z => φ (chartInv x z) t) (chartPt x x) :=
    ContDiffAt.comp (g := fun p : ComplexVector n × ℝ => φ (chartInv x p.1) p.2)
      (f := fun z : ComplexVector n => (z, t)) (chartPt x x) hs0 hi
  have hneg : leviC (fun z => -logDet (h t) x z) (chartPt x x) = ricci (h t) x := by
    have he := Yau.F04Proof.leviC_sub
      (contDiffAt_const (c := (0 : ℝ))) (hh.of_le (by norm_num))
    simpa only [zero_sub, leviC_zero, ricci] using he
  rw [Yau.F04Proof.leviC_sub (hh.neg.of_le (by norm_num)) (hs.of_le (by norm_num)), hneg]
  rfl

end Yau.NodeProofs.E03Aux
