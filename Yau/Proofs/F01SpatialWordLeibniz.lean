import Yau.Proofs.F01SpatialWordCalculus
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-! Exact finite Leibniz expansion of native spatial words. The list
retains each ordered choice of the differentiated factor, so repeated
terms carry their genuine multiplicities. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
variable {E F G H : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

def wordLeibnizPairs : List E → List (List E × List E)
  | [] => [([], [])]
  | v :: vs => (wordLeibnizPairs vs).map (fun ab => (v :: ab.1, ab.2)) ++
      (wordLeibnizPairs vs).map (fun ab => (ab.1, v :: ab.2))

theorem spatialDerivativeWord_bilinear {f : E × ℝ → F} {g : E × ℝ → G}
    {S : Set E} {t : ℝ} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ (fun x => f (x, t)) S)
    (hg : ContDiffOn ℝ ∞ (fun x => g (x, t)) S)
    (B : F →L[ℝ] G →L[ℝ] H) (vs : List E) {x : E} (hx : x ∈ S) :
    spatialDerivativeWord vs (fun p => B (f p) (g p)) (x, t) =
      ((wordLeibnizPairs vs).map
        (fun ab => B (spatialDerivativeWord ab.1 f (x, t))
          (spatialDerivativeWord ab.2 g (x, t)))).sum := by
  induction vs generalizing x with
  | nil => simp only [wordLeibnizPairs, spatialDerivativeWord, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
  | cons v vs ih =>
    let terms := wordLeibnizPairs vs
    let D (ab : List E × List E) : E →L[ℝ] H :=
      B.precompR E (spatialDerivativeWord ab.1 f (x, t))
        (fderiv ℝ (fun z => spatialDerivativeWord ab.2 g (z, t)) x) +
      B.precompL E (fderiv ℝ (fun z => spatialDerivativeWord ab.1 f (z, t)) x)
        (spatialDerivativeWord ab.2 g (x, t))
    have hD (ab : List E × List E) :
        HasFDerivAt (fun z => B (spatialDerivativeWord ab.1 f (z, t))
          (spatialDerivativeWord ab.2 g (z, t))) (D ab) x := by
      exact B.hasFDerivAt_of_bilinear
        (((spatialDerivativeWord_smooth_slice hS hf ab.1).contDiffAt
          (hS.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
        (((spatialDerivativeWord_smooth_slice hS hg ab.2).contDiffAt
          (hS.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have he : (fun z => spatialDerivativeWord vs (fun p => B (f p) (g p)) (z, t)) =ᶠ[𝓝 x]
        (fun z => (terms.map (fun ab => B (spatialDerivativeWord ab.1 f (z, t))
          (spatialDerivativeWord ab.2 g (z, t)))).sum) := by
      filter_upwards [hS.mem_nhds hx] with z hz
      exact ih hz
    have hsum := hasFDerivAt_list_sum_native terms
      (fun ab z => B (spatialDerivativeWord ab.1 f (z, t))
        (spatialDerivativeWord ab.2 g (z, t))) D (fun ab _ => hD ab)
    change fderiv ℝ (fun z => spatialDerivativeWord vs (fun p => B (f p) (g p)) (z, t)) x v = _
    rw [he.fderiv_eq, hsum.fderiv]
    have hEval (l : List (List E × List E)) :
        (l.map D).sum v =
          (l.map (fun ab => B (spatialDerivativeWord (v :: ab.1) f (x, t))
            (spatialDerivativeWord ab.2 g (x, t)))).sum +
          (l.map (fun ab => B (spatialDerivativeWord ab.1 f (x, t))
            (spatialDerivativeWord (v :: ab.2) g (x, t)))).sum := by
      induction l with
      | nil => simp
      | cons ab l ihl =>
        simp only [List.map_cons, List.sum_cons, ContinuousLinearMap.add_apply, ihl]
        change (B (spatialDerivativeWord ab.1 f (x, t))
          (spatialDerivativeWord (v :: ab.2) g (x, t)) +
          B (spatialDerivativeWord (v :: ab.1) f (x, t))
            (spatialDerivativeWord ab.2 g (x, t))) + _ = _
        abel
    rw [hEval]
    simp only [wordLeibnizPairs, List.map_append, List.sum_append, List.map_map, terms]
    rfl

end Yau.NodeProofs.F01Aux
