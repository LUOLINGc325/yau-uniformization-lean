import Yau.Proofs.F05HolderModel
import Yau.Proofs.F05HolderFullChart
import Yau.Proofs.F05CoefficientEllipticity
import Yau.Proofs.F05LinearCoefficients

/-! One exponent and one bound precede all moving endpoints and all positive
solutions. The estimate holds on every full radius-two receiving chart. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16ExpBoundaryHolderAux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_model_face_lift_frontier {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {z : Space n}
    (hz : z ∈ frontier (F05FlatOpen (A.normal i)) ∩ Metric.ball 0 2) :
    lift A i z ∈ frontier O := by
  have hz3 := Metric.ball_subset_ball (by norm_num : (2 : ℝ) ≤ 3) hz.2
  have hPhysical := ((hA.1 i).2.2.2.2.2.2.2 z hz3).2.2
  apply hPhysical.mpr
  have hFrontier := hz.1
  cases hnormal : A.normal i with
  | none => simpa only [hnormal,F05FlatOpen,frontier_univ,notMem_empty] using hFrontier
  | some j =>
    rw [hnormal] at hFrontier
    rw [show F05FlatOpen (some j) = {x : Space n | realCoord x j < 0} from rfl,
      coordinate_halfSpace_frontier] at hFrontier
    simpa only [hnormal,mem_ofPred_eq] using hFrontier

theorem F05_exp_boundary_holder_uniform (hn : 0 < n)
    {O : Set M.Carrier} {A : AtlasData M} (hA : GenuineAtlas O A)
    {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (R p : M.Carrier → ℝ → ℝ)
    {S m B : ℝ} (hS : 0 < S) (hm : 0 < m) (hmB : m ≤ B)
    (hh : MetricFamilySmooth h (Icc 0 S)) (hR : SmoothSpaceTime R (Icc 0 S))
    (hp : SmoothSpaceTime p (Icc 0 S)) :
    ∃ γ C : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < C ∧
      ∀ (T : ℝ), 0 < T → T ≤ S → ∀ q : M.Carrier → ℝ → ℝ,
      (∀ i, C2 (F05Q A i T) (pull A i q)) →
      (∀ i, ContDiffOn ℝ ∞ (pull A i q)
        ((F05ModelOpen A i ∩ Metric.ball 0 3) ×ˢ Ioc 0 T)) →
      (∀ x ∈ closure O, ∀ t ∈ Icc 0 T, m ≤ q x t ∧ q x t ≤ B) →
      (∀ x ∈ closure O, q x 0 = p x 0) →
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, q x t = p x t) →
      (∀ i, ExpDivergenceEquation
        ((F05ModelOpen A i ∩ Metric.ball 0 3) ×ˢ Ioc 0 T)
        (fun z => flatA (h z.2) A i z) (fun z j => flatB (h z.2) A i z j)
        (pull A i R) (pull A i q)) →
      ∀ i, HolderBound γ (F05Q A i T) (pull A i q) C := by
  classical
  by_cases hEmpty : A.count = 0
  · refine ⟨1/2,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro T hT hTS q hq hqSmooth hbound hi hl heq i
    have hiLt := i.isLt
    omega
  have hCount : 0 < A.count := Nat.pos_of_ne_zero hEmpty
  obtain ⟨lam,upper,hEll⟩ := F05_flat_principal_elliptic_uniform hA h hh
  let i₀ : Fin A.count := ⟨0,hCount⟩
  obtain ⟨hν,hνUpper⟩ := expDivergence_ellipticity_constants (hEll S le_rfl i₀) hm hmB
  obtain ⟨γ,Cdg,hγ,hγ1,hCdg,hCore⟩ := exists_interiorOscillationEstimate hn hν hνUpper
  have hLocal (i : Fin A.count) := F05_exp_model_holder_from_core (A.normal i)
    hS hm hmB hγ hγ1 hCdg hCore (F05_flat_coefficients_smooth hA h hh i)
    (F05_pull_spacetime_smooth hA R hR i) (F05_pull_spacetime_smooth hA p hp i) (hEll S le_rfl i)
  choose Ci hCi hModel using hLocal
  let Pcore := 1+∑ i,Ci i
  have hSum : 0 ≤ ∑ i,Ci i := Finset.sum_nonneg (fun i _ => (hCi i).le)
  have hPcore : 0 < Pcore := by dsimp [Pcore]; positivity
  have hCiCore (i : Fin A.count) : Ci i ≤ Pcore := by
    have hSingle := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin A.count))) => (hCi j).le) (Finset.mem_univ i)
    dsimp [Pcore]
    linarith
  obtain ⟨Ctransport,hCtransport,hTransport⟩ := F05_inner_holder_to_full (S := S) hA hγ hγ1
  refine ⟨γ,Ctransport*Pcore,hγ,hγ1,mul_pos hCtransport hPcore,?_⟩
  intro T hT hTS q hq hqSmooth hbound hi hl heq i
  apply hTransport T hT.le hTS q Pcore hPcore.le _ i
  intro j
  apply holderBound_mono_const _ (hCiCore j)
  apply hModel j T hT hTS (pull A j q) (hq j)
  · simpa only [F05CapOpen,← F05ModelOpen_eq] using hqSmooth j
  · intro z hz
    exact hbound (lift A j z.1) (F05D_lift_mem_closure hA hz.1) z.2 hz.2
  · intro z hz
    exact hi (lift A j z) (F05D_lift_mem_closure hA hz)
  · intro z hz t htm
    exact hl (lift A j z) (F05_model_face_lift_frontier hA j hz) t htm
  · simpa only [F05CapOpen,← F05ModelOpen_eq] using heq j

end Yau.Proofs.F05Aux
