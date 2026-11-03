import Yau.Proofs.F05CoordinateCoefficients
import Yau.Proofs.F04ChartEllipticity
import Yau.LeafProofs.L16ChartEllipticity

/-! Uniform ellipticity of the actual computed flattened coefficients. The
constants precede every moving endpoint and do not depend on a source. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_uniform_elliptic_family {ι : Type*} [Fintype ι]
    (Q : ι → Set (Point n)) (a : ι → Point n → Mat n)
    (h : ∀ i, ∃ lam upper : ℝ, Elliptic (Q i) (a i) lam upper) :
    ∃ lam upper : ℝ, ∀ i, Elliptic (Q i) (a i) lam upper := by
  classical
  choose l b hb using h
  let L := 1 + ∑ i, (l i)⁻¹
  let B := 1 + ∑ i, b i
  have hls (i : ι) : 0 < l i := (hb i).1
  have hbs (i : ι) : 0 ≤ b i := ((hls i).trans_le (hb i).2.1).le
  have hL1 : 1 ≤ L := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset ι)) => (inv_pos.mpr (hls i)).le)
    dsimp only [L]
    linarith
  have hB1 : 1 ≤ B := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hbs i)
    dsimp only [B]
    linarith
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hl (i : ι) : 1/L ≤ l i := by
    have hs : (l i)⁻¹ ≤ ∑ j, (l j)⁻¹ := Finset.single_le_sum
      (fun j hj => (inv_pos.mpr (hls j)).le) (Finset.mem_univ i)
    have hsL : (l i)⁻¹ ≤ L := by dsimp only [L]; linarith
    have hm := mul_le_mul_of_nonneg_left hsL (hls i).le
    rw [mul_inv_cancel₀ (hls i).ne'] at hm
    exact (div_le_iff₀ hL).mpr hm
  have hbB (i : ι) : b i ≤ B := by
    have hs : b i ≤ ∑ j, b j := Finset.single_le_sum (fun j hj => hbs j) (Finset.mem_univ i)
    dsimp only [B]
    linarith
  have hl1 : 1/L ≤ 1 := (div_le_iff₀ hL).mpr (by simpa only [one_mul] using hL1)
  refine ⟨1/L,B,fun i => ⟨one_div_pos.mpr hL,hl1.trans hB1,?_⟩⟩
  intro p hp
  obtain ⟨hSym,hQuad⟩ := (hb i).2.2 p hp
  refine ⟨hSym,?_⟩
  intro v
  have hv : 0 ≤ ∑ j, (v j)^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  exact ⟨(mul_le_mul_of_nonneg_right (hl i) hv).trans (hQuad v).1,
    (hQuad v).2.trans (mul_le_mul_of_nonneg_right (hbB i) hv)⟩

theorem F05_flat_principal_elliptic_chart {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {S : ℝ}
    (hh : MetricFamilySmooth h (Icc 0 S)) (i : Fin A.count) :
    ∃ lam upper : ℝ, Elliptic (cylinder (Metric.closedBall 0 2) 0 S)
      (fun p => flatA (h p.2) A i p) lam upper := by
  let c := F05AtlasFlatten hA i
  let K : Set (Space n) := Metric.closedBall 0 2
  let X := c.symm '' K
  have hKT : K ⊆ c.target := Metric.closedBall_subset_ball (by norm_num)
  have hc : ContDiffOn ℝ 3 c c.source := (hA.1 i).2.2.1.of_le (by simp)
  have hci : ContDiffOn ℝ 3 c.symm c.target := (hA.1 i).2.2.2.1.of_le (by simp)
  have hK : IsCompact K := isCompact_closedBall 0 2
  have hX : IsCompact X := hK.image_of_continuousOn (c.symm.continuousOn.mono hKT)
  have hTarget : cylinder X 0 S ⊆ chartTarget (A.center i) ×ˢ Icc 0 S := by
    rintro p ⟨⟨z,hz,heq⟩,ht⟩
    refine ⟨?_,ht⟩
    rw [← heq]
    exact (hA.1 i).2.1 (c.map_target (hKT hz))
  obtain ⟨lam,upper,hRaw⟩ := Yau.F04Proof.flowChartPrincipal_elliptic h hh (A.center i)
    (hX.prod isCompact_Icc) hTarget
  obtain ⟨C,hC,hTransport⟩ := compact_chart_ellipticity_budget c hc hci hK (convex_closedBall 0 2) hKT
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

theorem F05_flat_principal_elliptic_uniform {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {S : ℝ}
    (hh : MetricFamilySmooth h (Icc 0 S)) :
    ∃ lam upper : ℝ, ∀ T : ℝ, T ≤ S → ∀ i : Fin A.count,
      Elliptic (cylinder (Metric.closedBall 0 2) 0 T)
        (fun p => flatA (h p.2) A i p) lam upper := by
  obtain ⟨lam,upper,hAll⟩ := F05_uniform_elliptic_family
    (fun _ : Fin A.count => cylinder (Metric.closedBall 0 2) 0 S)
    (fun i p => flatA (h p.2) A i p) (F05_flat_principal_elliptic_chart hA h hh)
  refine ⟨lam,upper,fun T hTS i => ⟨(hAll i).1,(hAll i).2.1,?_⟩⟩
  intro p hp
  exact (hAll i).2.2 p ⟨hp.1,hp.2.1,hp.2.2.trans hTS⟩

end Yau.Proofs.F05Aux
