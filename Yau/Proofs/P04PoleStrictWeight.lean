import Yau.Proofs.P04PoleUniformModel
import Yau.Proofs.P04PoleGlobalLevi
import Yau.Proofs.P04FlatNakano

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- A single scalar produces genuine globally strict weights for every
positive regularization parameter up to the chosen chart radius. -/
theorem exists_uniform_strict_pole_weights (p : M.Carrier)
    {χ : ComplexVector n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (htarget : Metric.closedBall (chartPt p p) (2*ρ) ⊆ chartTarget p)
    (hsupp : tsupport χ ⊆ Metric.closedBall (chartPt p p) (3*ρ/2))
    (hone : ∀ z ∈ Metric.closedBall (chartPt p p) ρ, χ z=1)
    {c : ℝ} (hc : 0 ≤ c) {ψ : M.Carrier → ℝ} (hψ : IsSmoothStrictPsh ψ) :
    ∃ k : ℝ, 1 ≤ k ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ρ →
      (∀ x, (levi (fun y => (k-1)*ψ y+globalPolePart p χ c ε y) x).PosSemidef) ∧
      IsSmoothStrictPsh (regularizedPoleWeight p χ c k ψ ε) ∧
      BundleDbar.WeightedNakanoNonnegative (r := 1) (CanonicalCoefficients M) flatMetric
        (regularizedPoleWeight p χ c k ψ ε) := by
  have hs : tsupport χ ⊆ chartTarget p := hsupp.trans
    ((Metric.closedBall_subset_closedBall (by linarith : 3*ρ/2 ≤ 2*ρ)).trans htarget)
  obtain ⟨k,hk,hmodel⟩ := pole_model_uniform_domination p hχ hρ htarget hsupp hone hc hψ
  refine ⟨k,hk,fun ε hε hερ => ?_⟩
  have hP := globalPolePart_smooth p hχ hcχ hs c hε
  have hPs : tsupport (globalPolePart p χ c ε) ⊆ (extChartAt (ComplexModel n) p).source :=
    (L18Aux.chartPushforwardZero_properties p (regularizedPoleModel_smooth hχ _ c hε)
      (regularizedPoleModel_compact hcχ _ c ε)
      ((regularizedPoleModel_tsupport χ _ c ε).trans hs)).2.2
  have hlocal : ∀ z ∈ chartTarget p,
      (leviC (inChart p (fun y => (k-1)*ψ y+globalPolePart p χ c ε y)) z).PosSemidef := by
    intro z hz
    have hf : ContDiffAt ℝ 2 (inChart p ψ) z :=
      ((hψ.1 p).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz)).of_le (by simp)
    have hg : ContDiffAt ℝ 2 (regularizedPoleModel χ (chartPt p p) c ε) z :=
      (regularizedPoleModel_smooth hχ _ c hε).contDiffAt.of_le (by simp)
    have heq : inChart p (fun y => (k-1)*ψ y+globalPolePart p χ c ε y) =ᶠ[𝓝 z]
        (fun w => (k-1)*inChart p ψ w+regularizedPoleModel χ (chartPt p p) c ε w) := by
      filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with w hw
      change (k-1)*inChart p ψ w+inChart p (globalPolePart p χ c ε) w=_
      rw [globalPolePart_inChart p χ c ε hw]
    rw [L22Aux.leviC_congr_of_eventuallyEq heq,
      L17Aux.leviC_add (contDiffAt_const.mul hf) hg,L17Aux.leviC_const_mul hf (k-1)]
    exact hmodel ε hε hερ z hz
  have hglobal := pole_extension_global_semipositive p hψ hP hPs hk hlocal
  have hstrict := strictPsh_of_positive_background hψ hP k hglobal
  refine ⟨hglobal,hstrict,?_⟩
  apply flat_weightedNakano_of_chartLevi
  intro a z hz
  exact (smooth_strictPsh_all_charts hstrict a z hz).posSemidef

end Yau.Proofs.P04Aux
