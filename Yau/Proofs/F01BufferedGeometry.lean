import Yau.Proofs.F01OrdinaryMetricData
import Yau.Proofs.F01RescaledComponent
import Yau.Proofs.F01ApproximationGram
import Yau.Proofs.F01CoefficientMatrixBounds
import Yau.Proofs.F01CoefficientEntryJets
import Yau.Proofs.F01CoefficientSmooth

/-! One ordinary chart buffer supplies actual bounded-geometry charts for
all its sublevel centers. Constants are chosen before the center; all Gram
coefficients and derivatives belong to the explicitly constructed chart. -/
open Set Metric Filter TopologicalSpace
open scoped Topology Manifold ContDiff ComplexOrder Matrix.Norms.Frobenius
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} (M : ComplexManifold n)

theorem buffered_approximation_geometry {g : HermitianField M} (hg : MetricSmooth g)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hnonneg : ∀ x, 0 ≤ u x)
    (o : M.Carrier) {L : ℝ} (hL : 0 < L) (ho : u o < L)
    (q : M.Carrier) {r c A : ℝ} (hr : 0 < r) (hc : 0 < c) (hcr : c ≤ r / 12)
    (hA : 0 ≤ A) (hbuffer : closedBall (chartPt q q) (4 * r) ⊆ chartTarget q)
    (hD : ∀ y ∈ ball (chartPt q q) (4 * r),
      ‖fderiv ℝ (fun z => u (ordinaryChart q z)) y‖ ≤ A)
    (hbudget : 2 * c * A / L ≤ 1 / 2) :
    let N := sublevelManifold M u hu o L ho
    let α := approximatingMetric M g u hu o L ho
    ∃ (D : ℝ) (B : ℕ → ℝ), 0 < D ∧ (∀ k, 0 < B k) ∧
      ∀ p : N.Carrier, ∀ z₀ : ComplexVector n,
        z₀ ∈ closedBall (chartPt q q) r → ordinaryChart q z₀ = p.val →
        ∃ eL : OpenPartialHomeomorph (ComplexVector n) N.Carrier,
          eL 0 = p ∧ closedBall (0 : ComplexVector n) 1 ⊆ eL.source ∧
          MDifferentiableOn (ComplexModel n) (ComplexModel n) eL eL.source ∧
          MDifferentiableOn (ComplexModel n) (ComplexModel n) eL.symm eL.target ∧
          (∀ z ∈ ball (0 : ComplexVector n) 1,
            (L17Aux.pullbackMatrix α eL z - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
            ((D : ℂ) • 1 - L17Aux.pullbackMatrix α eL z).PosSemidef) ∧
          (∀ i j, ContDiffOn ℝ ∞ (fun z => LeafCandidates.pullbackCoefficient α eL z i j)
            (ball (0 : ComplexVector n) 1)) ∧
          ∀ k z, z ∈ ball (0 : ComplexVector n) 1 → ∀ i j,
            ‖iteratedFDeriv ℝ k (fun w => LeafCandidates.pullbackCoefficient α eL w i j) z‖ ≤ B k := by
  let N := sublevelManifold M u hu o L ho
  let α : HermitianField N := approximatingMetric M g u hu o L ho
  let e := ordinaryChart q
  let b := chartPt q q
  let uE : ComplexVector n → ℝ := fun z => u (e z)
  let G : ComplexVector n → Matrix (Fin n) (Fin n) ℂ := fun z => L17Aux.pullbackMatrix g e z
  have hBU : ball b (4 * r) ⊆ chartTarget q := fun _ hz => hbuffer (ball_subset_closedBall hz)
  have huE : ContDiffOn ℝ ∞ uE (ball b (4 * r)) :=
    (ordinary_coordinate_contDiffOn hu q).mono hBU
  have hGE : ∀ i j, ContDiffOn ℝ ∞ (fun y => G y i j) (ball b (4 * r)) :=
    fun i j => (ordinary_gram_entry_contDiffOn hg q i j).mono hBU
  have hG : ContDiffOn ℝ ∞ G (ball b (4 * r)) :=
    (ordinary_gram_contDiffOn hg q).mono hBU
  have hGpos : ∀ y ∈ ball b (4 * r), (G y).PosDef :=
    fun y hy => ordinary_gram_posDef g q (hBU hy)
  obtain ⟨D, hDpos, hmat⟩ := actual_coefficient_matrix_bounds b hr hc hcr hL hA huE hG hGpos hD hbudget
  obtain ⟨B, hB, hjets⟩ := actual_coefficient_all_entry_derivative_budgets b
    hr hc.le hcr hL hA huE hGE hD hbudget
  refine ⟨D, B, hDpos, hB, ?_⟩
  intro p z₀ hz₀ hcenter
  let δ := 1 - u p.val / L
  have hlevel : u p.val < L := sublevelManifold_point_level M u hu o L ho p
  have hδ : 0 < δ := sub_pos.mpr ((div_lt_one hL).mpr hlevel)
  have hδ1 : δ ≤ 1 := by
    have h := div_nonneg (hnonneg p.val) hL.le
    dsimp [δ]
    linarith
  have hbase : 1 - uE z₀ / L = δ := congrArg (fun x => 1 - u x / L) hcenter
  have hs : ((c * δ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_pos hc hδ).ne'
  let S := sublevelOpens M u hu o L
  have hS : IsConnected (S : Set M.Carrier) := sublevelComponent_isConnected ho
  let eL : OpenPartialHomeomorph (ComplexVector n) N.Carrier :=
    openRestrictedChart M S hS (rescaledChart e z₀ ((c * δ : ℝ) : ℂ) hs)
  have hp : p.val ∈ sublevelComponent u o L := p.property
  have hsource : ball b (4 * r) ⊆ e.source := by
    intro y hy
    rw [ordinaryChart_source]
    exact hBU hy
  have hprops := explicit_rescaled_sublevel_chart_properties M u hu o hL ho p.val hp e
    (ordinaryChart_contMDiffOn q) (ordinaryChart_inverse_contMDiffOn q) b z₀
    hr hc hcr hA hz₀ hcenter hsource hδ hδ1 hbase huE hD hbudget hs
  have hcenterL : eL 0 = p := hprops.1
  have hsourceL : closedBall (0 : ComplexVector n) 1 ⊆ eL.source := hprops.2.1
  have heL : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ eL eL.source := hprops.2.2.1
  have heiL : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ eL.symm eL.target := hprops.2.2.2
  have hcoef (w : ComplexVector n) (hw : w ∈ ball (0 : ComplexVector n) 1) (i j : Fin n) :
      LeafCandidates.pullbackCoefficient α eL w i j =
        interiorExtension uE (fun y => G y i j) L c (z₀, δ, w) := by
    have hwl : w ∈ eL.source := hsourceL (ball_subset_closedBall hw)
    exact conformal_open_rescaled_chart_coefficient M S hS g u L c δ e
      (ordinaryChart_contMDiffOn q) z₀ hs hwl i j
  have hmatrix (w : ComplexVector n) (hw : w ∈ ball (0 : ComplexVector n) 1) :
      L17Aux.pullbackMatrix α eL w = interiorExtension uE G L c (z₀, δ, w) := by
    ext i j
    exact hcoef w hw i j
  refine ⟨eL, hcenterL, hsourceL, heL.mdifferentiableOn (by simp),
    heiL.mdifferentiableOn (by simp), ?_, ?_, ?_⟩
  · intro w hw
    rw [hmatrix w hw]
    exact hmat z₀ δ w hz₀ hδ hδ1 hbase hw
  · intro i j
    exact (actual_coefficient_contDiffOn b z₀ hr hc.le hcr hL hA huE (hGE i j) hD hbudget
      hz₀ hδ hδ1 hbase).congr (fun w hw => hcoef w hw i j)
  · intro k w hw i j
    have heq : (fun y => LeafCandidates.pullbackCoefficient α eL y i j) =ᶠ[𝓝 w]
        (fun y => interiorExtension uE (fun z => G z i j) L c (z₀, δ, y)) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hw) (fun y hy => hcoef y hy i j)
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
    exact hjets k z₀ δ w hz₀ hδ hδ1 hbase hw i j

end Yau.NodeProofs.F01Aux
