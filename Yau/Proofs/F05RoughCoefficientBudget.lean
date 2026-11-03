import Yau.Proofs.F05UniformCoefficients
import Yau.Proofs.F05FlowPatchSolver
import Yau.LeafProofs.L16ResidualEstimates

/-! Uniform physical coefficient budgets use a candidate's value Holder
bound and scalar interval only. Smoothness of the candidate is not needed. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_rough_scalar_coefficient_budgets {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {S D l u : ℝ}
    (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hD : 0 ≤ D) (hl : 0 < l) (hlu : l ≤ u) :
    ∃ lam upper C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α < 1 →
      ∀ (T : ℝ), T ≤ S → ∀ c : M.Carrier → ℝ → ℝ,
      (∀ i, HolderBound α (F05Q A i T) (pull A i c) D) →
      (∀ i, ∀ p ∈ F05Q A i T, l ≤ pull A i c p ∧ pull A i c p ≤ u) →
      ∀ i, Elliptic (F05Q A i T) (F05FlowPrincipal A i h c) lam upper ∧
        HolderBound α (F05Q A i T) (F05FlowPrincipal A i h c) C ∧
        ∀ j, HolderBound α (F05Q A i T) (fun p => F05FlowDrift A i h c p j) C := by
  have hOne : SmoothSpaceTime (M := M) (fun (_ : M.Carrier) (_ : ℝ) => (1 : ℝ))
      (Icc 0 S) := fun _ => contDiffOn_const
  obtain ⟨B,hB,hBudget⟩ := F05_linear_holder_uniform hA h (fun _ _ => 1) hS hh hOne
  obtain ⟨lam,upper,hEll⟩ := F05_flat_principal_elliptic_uniform hA h hh
  let C := 1+2*D*B
  have hC : 0 < C := by dsimp [C]; positivity
  have hMain : 2*D*B ≤ C := by dsimp [C]; linarith
  refine ⟨l*lam,u*upper,C,hC,?_⟩
  intro α hα hα1 T hTS c hc hRange i
  have hSub : F05Q A i T ⊆ cylinder (Metric.closedBall (0 : Space n) 2) 0 T := fun p hp =>
    ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1.1,hp.2⟩
  have hBase : Elliptic (F05Q A i T) (fun p => flatA (h p.2) A i p) lam upper :=
    ⟨(hEll T hTS i).1,(hEll T hTS i).2.1,fun p hp => (hEll T hTS i).2.2 p (hSub hp)⟩
  have hOld := hBudget α hα hα1 T hTS i
  have ha : HolderBound α (F05Q A i T) (fun p => flatA (h p.2) A i p) B := by
    simpa only [pull,one_smul] using holderBound_mono hOld.1 hSub
  have hb (j : RIdx n) : HolderBound α (F05Q A i T) (fun p => flatB (h p.2) A i p j) B := by
    simpa only [pull,one_mul] using holderBound_mono (hOld.2 j) hSub
  have hPrincipal := holderBound_smul_refined (hc i) ha (hc i).1 ha.1
    (fun p hp => by simpa only [Real.norm_eq_abs] using (hc i).2.1 p hp) ha.2.1
  refine ⟨F05_elliptic_scalar_mul hBase hl hlu (hRange i),?_,?_⟩
  · apply holderBound_mono_const (show HolderBound α (F05Q A i T) (F05FlowPrincipal A i h c)
        (2*D*B) from ?_) hMain
    have hScalar : D*B+D*B = 2*D*B := by ring
    have hPrincipal' : HolderBound α (F05Q A i T) (F05FlowPrincipal A i h c)
        (D*B+D*B) := hPrincipal
    simpa only [hScalar] using hPrincipal'
  · intro j
    exact holderBound_mono_const (holderBound_mul (hc i) (hb j)) hMain

end Yau.Proofs.F05Aux
