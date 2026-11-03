import Yau.Proofs.F05LinearOperatorHolder
import Yau.Proofs.F05FlowPatchSolver
import Yau.Proofs.F05JetOperator

/-! The original intrinsic operator on the concrete realization has a
uniform actual Holder budget before the moving endpoint and every jet. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05JetOperator_eq_chart {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ) (α : ℝ)
    {T : ℝ} (hT : 0 < T) (u : F05CompatibleJetGraph A α hT.le)
    (i : Fin A.count) {p : Point n} (hp : p ∈ F05Q A i T) :
    F05JetOperator A c h α hT.le u i p = linearOp (F05Q A i T)
      (F05FlowPrincipal A i h c) (F05FlowDrift A i h c) (F05CanonicalPull A χ α hT.le u i) p := by
  have hReal := F05CanonicalJetFunction_realizes hA hχ α hT u i
  unfold F05JetOperator linearOp F05FlowPrincipal F05FlowDrift pull
  rw [hReal.2.1 hp,hReal.2.2.1 hp,hReal.2.2.2 hp]
  simp only [Matrix.smul_apply,smul_eq_mul,mul_add,Finset.mul_sum,mul_assoc]
  ring

theorem F05_jet_operator_holder_uniform {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hc : SmoothSpaceTime c (Icc 0 S)) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (hT : 0 < T), T ≤ S → T ≤ 1 →
      ∀ u : F05CompatibleJetGraph A α hT.le, ∀ i : Fin A.count,
        HolderBound α (F05Q A i T) (F05JetOperator A c h α hT.le u i) (C*‖u‖) := by
  obtain ⟨B,hB,hCoeff⟩ := F05_linear_holder_uniform hA h c hS hh hc
  obtain ⟨D,hD,hLow⟩ := F05_canonical_lower_holder hA hχ hα hα1
  let N : ℝ := Fintype.card (RIdx n)
  let C := 1+2*N^2*B+2*N*B*D
  refine ⟨C,by dsimp only [C,N]; positivity,?_⟩
  intro T hT hTS hT1 u i
  have hSub : F05Q A i T ⊆ cylinder (Metric.closedBall 0 2) 0 T := by
    intro p hp
    exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1.1,hp.2⟩
  have hBounds := hCoeff α hα hα1 T hTS i
  have hNorm : ‖(u.val i).val‖ ≤ ‖u‖ := by
    change ‖u.val i‖ ≤ ‖u.val‖
    exact norm_le_pi_norm u.val i
  have hHigh := schauderBound_mono_const (F05CanonicalJetFunction_schauder hA hχ α hT u i) hNorm
  have hOp := F05_linearOp_holder (a := F05FlowPrincipal A i h c) (b := F05FlowDrift A i h c)
    (holderBound_mono hBounds.1 hSub) (fun j => holderBound_mono (hBounds.2 j) hSub)
    hHigh (hLow T hT hT1 u i)
  have hExact : HolderBound α (F05Q A i T) (F05JetOperator A c h α hT.le u i)
      (‖u‖+2*(Fintype.card (RIdx n) : ℝ)^2*B*‖u‖+2*(Fintype.card (RIdx n) : ℝ)*B*(D*‖u‖)) :=
    holderBound_congr_on hOp (fun p hp => (F05JetOperator_eq_chart hA hχ h c α hT u i hp).symm)
  convert hExact using 1
  dsimp only [C,N]
  ring

end Yau.Proofs.F05Aux
