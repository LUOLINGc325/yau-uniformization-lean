import Yau.Proofs.F01BoundedPotentialUniqueness
import Yau.Proofs.F01ControlledComparisonQ

/-! For the actual controlled approximating backgrounds, the original
finite short-time sandwiches supply every bound in the nonlinear uniqueness
argument. No extra boundedness or complete positive-time slice is assumed. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem controlled_potential_solutions_unique (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) {L : ℝ} (ho : u o < L) :
    let N := sublevelManifold X.manifold u hu.1 o L ho
    let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
    ∀ (h k : ℝ → HermitianField N) (U V : N.Carrier → ℝ → ℝ) (T C1 C2 : ℝ),
      0 < T → 1 ≤ C1 → 1 ≤ C2 →
      SmoothSpaceTime U (Icc 0 T) → SmoothSpaceTime V (Icc 0 T) →
      (∀ x, U x 0 = 0) → (∀ x, V x 0 = 0) →
      (∀ x t, t ∈ Icc 0 T →
        (gMat (h t) x - ((C1⁻¹ : ℝ) : ℂ) • gMat α x).PosSemidef ∧
        ((C1 : ℂ) • gMat α x - gMat (h t) x).PosSemidef ∧
        gMat (h t) x = gMat α x - (t : ℂ) • ricci α x + levi (fun y => U y t) x ∧
        HasDerivWithinAt (U x) (flowLogDetRatio α h x t) (Icc 0 T) t) →
      (∀ x t, t ∈ Icc 0 T →
        (gMat (k t) x - ((C2⁻¹ : ℝ) : ℂ) • gMat α x).PosSemidef ∧
        ((C2 : ℂ) • gMat α x - gMat (k t) x).PosSemidef ∧
        gMat (k t) x = gMat α x - (t : ℂ) • ricci α x + levi (fun y => V y t) x ∧
        HasDerivWithinAt (V x) (flowLogDetRatio α k x t) (Icc 0 T) t) →
      (∀ x t, t ∈ Icc 0 T → U x t = V x t) ∧ ∀ t ∈ Icc 0 T, h t = k t := by
  dsimp only
  intro h k U V T C1 C2 hT hC1 hC2 hU hV hU0 hV0 hdataU hdataV
  obtain ⟨A, hA, B, hB, hbudgets⟩ := controlled_conformal_gradient_levi X o u hu
  have hL : 0 < L := (zero_lt_one.trans_le (hu.2.2.1 o)).trans ho
  let N := sublevelManifold X.manifold u hu.1 o L ho
  let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
  let f : N.Carrier → ℝ := approximatingScalar X.manifold u hu.1 o L ho
  have hf : SmoothFn f := approximatingScalar_smoothFn u hu.1 o hL ho
  have hf0 (x : N.Carrier) : 0 ≤ f x :=
    conformalProfile_nonneg ((div_lt_one hL).mpr
      (sublevelManifold_point_level X.manifold u hu.1 o L ho x))
  have hfproper : ∀ b : ℝ, IsCompact {x : N.Carrier | f x ≤ b} :=
    conformalProfile_compact_component_sublevel u (continuous_of_smoothFn hu.1) hu.2.1 o hL
  have hPU (x : N.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) :
      |flowLogDetRatio α h x t| ≤ (n : ℝ) * Real.log C1 :=
    logdet_ratio_abs_bound_of_sandwich
      (Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x))
      (Yau.LeafProofs.L12Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x))
      hC1 (hdataU x t ht).1 (hdataU x t ht).2.1
  have hPV (x : N.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) :
      |flowLogDetRatio α k x t| ≤ (n : ℝ) * Real.log C2 :=
    logdet_ratio_abs_bound_of_sandwich
      (Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x))
      (Yau.LeafProofs.L12Aux.hMat_posDef (k t) x (chartPt x x) (mem_extChartAt_target x))
      hC2 (hdataV x t ht).1 (hdataV x t ht).2.1
  have hUb (x : N.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) :
      |U x t| ≤ ((n : ℝ) * Real.log C1) * T :=
    (closed_potential_abs_bound_of_time_value hT.le (hU0 x)
      (fun s hs => (hdataU x s hs).2.2.2) (hPU x) t ht).trans
        (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hC1)))
  have hVb (x : N.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) :
      |V x t| ≤ ((n : ℝ) * Real.log C2) * T :=
    (closed_potential_abs_bound_of_time_value hT.le (hV0 x)
      (fun s hs => (hdataV x s hs).2.2.2) (hPV x) t ht).trans
        (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hC2)))
  exact bounded_potential_solutions_unique α h k U V hT hU hV
    (fun x => by rw [hU0 x, hV0 x])
    (fun s hs x => (hdataU x s hs).2.2.1) (fun s hs x => (hdataV x s hs).2.2.1)
    (fun x s hs => (hdataU x s hs).2.2.2) (fun x s hs => (hdataV x s hs).2.2.2)
    hUb hVb f hf hf0 hfproper
    (fun x t ht => laplacian_bound_from_metric_comparison α (h t) f x
      (zero_lt_one.trans_le hC1) (div_nonneg hB.le (sq_nonneg L))
      (hdataU x t ht).1 (hbudgets L ho x).2.2)
    (fun x t ht => laplacian_bound_from_metric_comparison α (k t) f x
      (zero_lt_one.trans_le hC2) (div_nonneg hB.le (sq_nonneg L))
      (hdataV x t ht).1 (hbudgets L ho x).2.2)

end Yau.NodeProofs.F01Aux
