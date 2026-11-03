import Yau.Proofs.F05LinearEllipticity
import Yau.Proofs.F05CoefficientExtension

/-! Actual variable coefficients of the supplied scalar-weighted flow have
one uniform global-model budget, chosen before every endpoint and source. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_linear_holder_uniform {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hc : SmoothSpaceTime c (Icc 0 S)) :
    ∃ B : ℝ, 0 < B ∧ ∀ (α : ℝ), 0 < α → α < 1 → ∀ (T : ℝ), T ≤ S → ∀ i : Fin A.count,
      HolderBound α (cylinder (Metric.closedBall 0 2) 0 T)
        (fun p => pull A i c p • flatA (h p.2) A i p) B ∧
      ∀ j, HolderBound α (cylinder (Metric.closedBall 0 2) 0 T)
        (fun p => pull A i c p * flatB (h p.2) A i p j) B := by
  classical
  choose C hC hBounds using (fun i : Fin A.count => F05_linear_coefficients_holder hA h c hS hh hc i)
  let B := 1+∑ i,C i
  have hSum : 0 ≤ ∑ i,C i := Finset.sum_nonneg (fun i _ => (hC i).le)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hCB (i : Fin A.count) : C i ≤ B := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin A.count))) => (hC j).le)
      (Finset.mem_univ i)
    dsimp only [B]
    linarith
  refine ⟨B,hB,?_⟩
  intro α hα hα1 T hTS i
  exact ⟨holderBound_mono_const (hBounds i α hα hα1 T hTS).1 (hCB i),
    fun j => holderBound_mono_const ((hBounds i α hα hα1 T hTS).2 j) (hCB i)⟩

theorem F05_global_model_coefficients {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hc : SmoothSpaceTime c (Icc 0 S)) (hPos : ∀ x t, t ∈ Icc 0 S → 0 < c x t)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ lam upper B : ℝ, 0 < B ∧ ∀ (T : ℝ), T ≤ S → ∀ i : Fin A.count,
      Elliptic (cylinder (closure (F05ModelOpen A i)) 0 T)
        (F05PrincipalExtension (fun p => pull A i c p • flatA (h p.2) A i p)) lam upper ∧
      HolderBound α (cylinder (closure (F05ModelOpen A i)) 0 T)
        (F05PrincipalExtension (fun p => pull A i c p • flatA (h p.2) A i p)) B ∧
      ∀ j, HolderBound α (cylinder (closure (F05ModelOpen A i)) 0 T)
        (fun p => F05DriftExtension (fun q k => pull A i c q * flatB (h q.2) A i q k) p j) B := by
  classical
  obtain ⟨lam,upper,hEll⟩ := F05_linear_coefficients_elliptic_uniform hA h c hS hh hc hPos
  obtain ⟨M₀,hM,hHolder⟩ := F05_linear_holder_uniform hA h c hS hh hc
  choose J hJ hExtension using (fun i : Fin A.count => F05_coefficient_extension_budget A i hα hα1)
  let J₀ := 1+∑ i,J i
  have hJsum : 0 ≤ ∑ i,J i := Finset.sum_nonneg (fun i _ => (hJ i).le)
  have hJ₀ : 0 < J₀ := by dsimp only [J₀]; positivity
  have hJJ (i : Fin A.count) : J i ≤ J₀ := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin A.count))) => (hJ j).le)
      (Finset.mem_univ i)
    dsimp only [J₀]
    linarith
  refine ⟨min lam 1,max upper 1,J₀*(M₀+1),by positivity,?_⟩
  intro T hTS i
  have hSub : F05Q A i T ⊆ cylinder (Metric.closedBall 0 2) 0 T := by
    intro p hp
    exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1.1,hp.2⟩
  have hOldEll : Elliptic (F05Q A i T) (fun p => pull A i c p • flatA (h p.2) A i p) lam upper :=
    ⟨(hEll T hTS i).1,(hEll T hTS i).2.1,fun p hp => (hEll T hTS i).2.2 p (hSub hp)⟩
  have hOriginal := hHolder α hα hα1 T hTS i
  have hNew := hExtension i T lam upper M₀
    (fun p => pull A i c p • flatA (h p.2) A i p)
    (fun p j => pull A i c p * flatB (h p.2) A i p j) hM.le hOldEll
    (holderBound_mono hOriginal.1 hSub) (fun j => holderBound_mono (hOriginal.2 j) hSub)
  have hBudget : J i*(M₀+1) ≤ J₀*(M₀+1) := mul_le_mul_of_nonneg_right (hJJ i) (by positivity)
  exact ⟨hNew.1,holderBound_mono_const hNew.2.1 hBudget,
    fun j => holderBound_mono_const (hNew.2.2 j) hBudget⟩

end Yau.Proofs.F05Aux
