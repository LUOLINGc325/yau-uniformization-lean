import Yau.Proofs.P03CompactChartCover

/-! A finite genuine chart-ball cover with room for recentering. -/
noncomputable section
open Set Filter
open scoped Topology Manifold
namespace Yau.Proofs.C03Aux.TargetCharts
open Yau Yau.NodeProofs.P03Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_finite_chart_cover (K : Set M.Carrier) (hK : IsCompact K) :
    ∃ (r : M.Carrier → ℝ) (I : Finset M.Carrier),
      (∀ a, 0 < r a) ∧
      (∀ a, Metric.closedBall (chartPt a a) (4 * r a) ⊆ chartTarget a) ∧
      K ⊆ ⋃ a ∈ I, chartInv a '' Metric.ball (chartPt a a) (r a) := by
  classical
  have hrad (a : M.Carrier) : ∃ R : ℝ, 0 < R ∧
      Metric.closedBall (chartPt a a) R ⊆ chartTarget a :=
    Metric.nhds_basis_closedBall.mem_iff.mp
      ((isOpen_extChartAt_target a).mem_nhds (mem_extChartAt_target a))
  choose R hR htarget using hrad
  let r := fun a => R a / 4
  have hr (a : M.Carrier) : 0 < r a := div_pos (hR a) (by norm_num)
  have hlarge (a : M.Carrier) :
      Metric.closedBall (chartPt a a) (4 * r a) ⊆ chartTarget a := by
    simpa only [r, mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using htarget a
  have hsmall (a : M.Carrier) :
      Metric.closedBall (chartPt a a) (r a) ⊆ chartTarget a :=
    (Metric.closedBall_subset_closedBall (by linarith [hr a])).trans (hlarge a)
  let W := fun a => chartInv a '' Metric.ball (chartPt a a) (r a)
  have hopen (a : M.Carrier) : IsOpen (W a) := chartBall_isOpen a (hsmall a)
  have hcover : K ⊆ ⋃ a, W a := by
    intro p _
    apply mem_iUnion.mpr
    refine ⟨p, chartPt p p, Metric.mem_ball_self (hr p), ?_⟩
    exact (extChartAt (ComplexModel n) p).left_inv (mem_extChartAt_source p)
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover W hopen hcover
  exact ⟨r, I, hr, hlarge, hI⟩

theorem finite_positive_minorant {α : Type*} (I : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ I, 0 < f a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ I, δ ≤ f a := by
  classical
  let S := ∑ a ∈ I, (f a)⁻¹
  have hS : 0 ≤ S := Finset.sum_nonneg (fun a ha => inv_nonneg.mpr (hf a ha).le)
  have hD : 0 < 1 + S := by linarith
  refine ⟨1 / (1 + S), one_div_pos.mpr hD, ?_⟩
  intro a ha
  have hi : (f a)⁻¹ ≤ S :=
    Finset.single_le_sum (fun b hb => inv_nonneg.mpr (hf b hb).le) ha
  have hp := mul_le_mul_of_nonneg_left hi (hf a ha).le
  rw [mul_inv_cancel₀ (hf a ha).ne'] at hp
  apply (div_le_iff₀ hD).mpr
  nlinarith [hf a ha]

end Yau.Proofs.C03Aux.TargetCharts
