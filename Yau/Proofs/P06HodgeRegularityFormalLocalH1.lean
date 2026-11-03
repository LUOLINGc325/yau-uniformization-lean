import Yau.Proofs.P06HodgeRegularityFormalCutoff
import Yau.Proofs.P06HodgeRegularityForwardCompact

/-! Local H¹ gain for the natural forward finite scalar-principal system.
The only field hypotheses are actual local L² values and the local PDE. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L03

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [Fintype α] [DecidableEq α]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant] [SigmaFinite ν]

theorem regularityForwardWeak_formal_whole
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    {O : Set E} {U W : E → α → ℝ}
    (hweak : regularityForwardWeak ν O v q e1 e0 U W)
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    (r : α) {φ : E → ℝ} (hφ : regularityTest O φ) :
    (∫ z, ∑ c, divergenceFormalTest v (regularityScalarSystemA q)
      (hodgeForwardB v (regularityScalarSystemA q) e1)
      (hodgeForwardC v (regularityScalarSystemA q) e1 e0) φ z r c * U z c ∂ν) =
      ∫ z, φ z * W z r ∂ν := by
  have ha := regularityScalarSystemA_contDiff (α := α) q hq
  have hh := hweak r φ hφ
  rw [regularityForwardTranspose_integral_restrict ν v _ e1 e0 ha he1 he0 hφ U r,
    regularityForwardSource_integral_restrict ν hφ (fun z => W z r)] at hh
  have heq : (fun z => ∑ c, divergenceFormalTest v (regularityScalarSystemA q)
      (hodgeForwardB v (regularityScalarSystemA q) e1)
      (hodgeForwardC v (regularityScalarSystemA q) e1 e0) φ z r c * U z c) =
      fun z => ∑ c, regularityForwardTranspose v (regularityScalarSystemA q) e1 e0 φ z r c * U z c := by
    funext z
    simp only [regularityForwardFormal_eq_transpose v _ e1 e0 ha he1 φ hφ.1]
  rw [heq]
  exact hh

theorem regularityForwardWeak_cutoff_h1
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    {O : Set E} (hO : IsOpen O) {χ : E → ℝ} (hχ : regularityTest O χ)
    (U W : E → α → ℝ)
    (hU : ∀ c, MemLp (fun z => U z c) 2 (ν.restrict O))
    (hW : ∀ c, MemLp (fun z => W z c) 2 (ν.restrict O))
    (hweak : regularityForwardWeak ν O v q e1 e0 U W)
    (B0 : Set E) (hB0 : IsOpen B0) (hcB0 : IsCompact (closure B0)) (hχB0 : tsupport χ ⊆ B0)
    (ell : ℝ) (hell : 0 < ell)
    (hcoercive : ∀ z ∈ closure B0, ∀ ξ : ι × α → ℝ,
      ell * ∑ p, (ξ p)^2 ≤ ∑ r, ∑ c, ∑ i, ∑ j,
        regularityScalarSystemA q r c i j z * ξ (j,c) * ξ (i,r)) :
    ∃ G : E → ι → α → ℝ,
      (∀ i c, MemLp (fun z => G z i c) 2 ν) ∧
      ∀ i c, regularityWeakDeriv ν Set.univ (v i) (fun z => χ z * U z c) (fun z => G z i c) := by
  classical
  let a := regularityScalarSystemA (α := α) q
  let B := hodgeForwardB v a e1
  let C := hodgeForwardC v a e1 e0
  have ha := regularityScalarSystemA_contDiff (α := α) q hq
  have hca := regularityScalarSystemA_hasCompactSupport (α := α) q hcq
  have hB := hodgeForwardB_contDiff v a e1 ha he1
  have hcB := hodgeForwardB_hasCompactSupport v a e1 hca hce1
  have hC := hodgeForwardC_contDiff v a e1 e0 ha he1 he0
  have hcC := hodgeForwardC_hasCompactSupport v a e1 e0 hca hce1 hce0
  have hformal := regularityDivergenceFormal_cutoff ν v a B C ha hB hC hO hχ U W hU hW
    (fun r φ ht => regularityForwardWeak_formal_whole ν v q e1 e0 hq he1 hweak he0 r ht)
  obtain ⟨_, D, _, _, _, hD, _, _, hd⟩ := regularityFormalSource_compact_h1 ν v a B C
    ha hca hB hcB hC hcC (fun z c => χ z * U z c)
    (regularityFormalCutoffValue v a B χ U W) (regularityFormalCutoffFlux v a χ U)
    (fun c => regularityCompact_mul_memLp ν hO hχ.1 hχ.2.1 hχ.2.2 (hU c))
    (regularityFormalCutoffValue_memLp ν v a B ha hB hO hχ U W hU hW)
    (regularityFormalCutoffFlux_memLp ν v a ha hO hχ U hU)
    χ hχ.2.1 (fun _ => tsupport_mul_subset_left)
    (regularityFormalCutoffValue_tsupport v a B ha hB hχ.1 hχ.2.1 U W)
    (regularityFormalCutoffFlux_tsupport v a ha hχ.1 hχ.2.1 U)
    hformal B0 hB0 hcB0 hχB0 ell hell hcoercive
  exact ⟨fun z i c => D z (i,c), fun i c => hD (i,c), hd⟩

end Yau.NodeProofs.P06Aux
