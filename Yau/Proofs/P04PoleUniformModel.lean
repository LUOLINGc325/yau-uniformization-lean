import Yau.Proofs.P04PoleAnnulusDomination
import Yau.Proofs.P04PoleLocalLevi
import Yau.Proofs.P04LeviCharts

noncomputable section
open Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

/-- Compact annulus domination and the actual inner/outer calculations
produce one scalar valid on the ENTIRE original model chart. -/
theorem pole_model_uniform_domination (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) {ρ : ℝ} (hρ : 0 < ρ)
    (htarget : Metric.closedBall (chartPt p p) (2*ρ) ⊆ chartTarget p)
    (hsupp : tsupport χ ⊆ Metric.closedBall (chartPt p p) (3*ρ/2))
    (hone : ∀ z ∈ Metric.closedBall (chartPt p p) ρ, χ z=1)
    {c : ℝ} (hc : 0 ≤ c) {ψ : M.Carrier → ℝ} (hψ : IsSmoothStrictPsh ψ) :
    ∃ k : ℝ, 1 ≤ k ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ρ → ∀ z ∈ chartTarget p,
      (((k-1 : ℝ) : ℂ) • leviC (inChart p ψ) z+
        leviC (regularizedPoleModel χ (chartPt p p) c ε) z).PosSemidef := by
  have hpos := smooth_strictPsh_all_charts hψ
  have hs : poleAnnulus (chartPt p p) ρ ⊆ chartTarget p := fun z hz => htarget hz.1
  obtain ⟨k,hk,hann⟩ := pole_annulus_uniform_domination p hχ c hρ hs hψ.1 (hpos p)
  refine ⟨k,hk,fun ε hε hερ z hz => ?_⟩
  have hbase : (((k-1 : ℝ) : ℂ) • leviC (inChart p ψ) z).PosSemidef :=
    (hpos p z hz).posSemidef.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hk))
  by_cases hin : z ∈ Metric.ball (chartPt p p) (ρ/2)
  · have hinρ : z ∈ Metric.ball (chartPt p p) ρ :=
      Metric.ball_subset_ball (by linarith : ρ/2 ≤ ρ) hin
    exact hbase.add (regularizedPoleModel_levi_inner _ hone hc hε hinρ)
  · by_cases hout : z ∈ Metric.closedBall (chartPt p p) (2*ρ)
    · exact hann ε ⟨hε.le,hερ⟩ z ⟨hout,hin⟩
    · have hzero : z ∉ tsupport χ := by
        intro hzχ
        exact hout (Metric.closedBall_subset_closedBall (by linarith : 3*ρ/2 ≤ 2*ρ) (hsupp hzχ))
      rw [regularizedPoleModel_levi_off_support _ c ε hzero,add_zero]
      exact hbase

end Yau.Proofs.P04Aux
