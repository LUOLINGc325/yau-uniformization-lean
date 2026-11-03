import Yau.Proofs.F05CoefficientEllipticity

/-! The actual computed principal matrix is uniformly elliptic on every
fixed compact raw reference ball strictly inside the genuine chart.
The physical cap and every candidate solution are absent from the target. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_flat_principal_elliptic_radius {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {S r : ℝ} (hr : r < 3)
    (hh : MetricFamilySmooth h (Icc 0 S)) (i : Fin A.count) :
    ∃ lam upper : ℝ, Elliptic (cylinder (Metric.closedBall 0 r) 0 S)
      (fun p => flatA (h p.2) A i p) lam upper := by
  let c := F05AtlasFlatten hA i
  let K : Set (Space n) := Metric.closedBall 0 r
  let X := c.symm '' K
  have hKT : K ⊆ c.target := Metric.closedBall_subset_ball hr
  have hc : ContDiffOn ℝ 3 c c.source := (hA.1 i).2.2.1.of_le (by simp)
  have hci : ContDiffOn ℝ 3 c.symm c.target := (hA.1 i).2.2.2.1.of_le (by simp)
  have hK : IsCompact K := isCompact_closedBall 0 r
  have hX : IsCompact X := hK.image_of_continuousOn (c.symm.continuousOn.mono hKT)
  have hTarget : cylinder X 0 S ⊆ chartTarget (A.center i) ×ˢ Icc 0 S := by
    rintro p ⟨⟨z,hz,heq⟩,ht⟩
    refine ⟨?_,ht⟩
    rw [← heq]
    exact (hA.1 i).2.1 (c.map_target (hKT hz))
  obtain ⟨lam,upper,hRaw⟩ := Yau.F04Proof.flowChartPrincipal_elliptic h hh (A.center i)
    (hX.prod isCompact_Icc) hTarget
  obtain ⟨C,hC,hTransport⟩ := compact_chart_ellipticity_budget c hc hci hK (convex_closedBall 0 r) hKT
  have hFlat := hTransport K X S lam upper (Yau.F04Proof.flowChartPrincipal h (A.center i))
    subset_rfl (fun z hz => ⟨z,hz,rfl⟩) hRaw
  have hEq (p : Point n) (hp : p ∈ cylinder K 0 S) :
      flatA (h p.2) A i p =
        chartTransformedPrincipal c (Yau.F04Proof.flowChartPrincipal h (A.center i)) p := by
    have hpB : p.1 ∈ Metric.ball 0 3 := hKT hp.1
    have hpT := (hA.1 i).2.1 (c.map_target hpB)
    change A.inverse i p.1 ∈ chartTarget (A.center i) at hpT
    rw [F05_flatA_chartPrincipal hA (h p.2) i p hpB,
      F05_baseA_eq_flowChartPrincipal h (A.center i) hpT p.2]
    rfl
  refine ⟨lam/C^2,upper*C^2,hFlat.1,hFlat.2.1,?_⟩
  intro p hp
  change (flatA (h p.2) A i p).IsSymm ∧ ∀ v : RIdx n → ℝ,
    lam/C^2 * (∑ j, (v j)^2) ≤ ∑ j, ∑ k, flatA (h p.2) A i p j k * v j * v k ∧
      (∑ j, ∑ k, flatA (h p.2) A i p j k * v j * v k) ≤ upper*C^2 * (∑ j, (v j)^2)
  rw [hEq p hp]
  exact hFlat.2.2 p hp

end Yau.Proofs.F05Aux
