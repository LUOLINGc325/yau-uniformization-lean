import Yau.Proofs.C02FlowBallComparison
import Yau.Proofs.C02CompactDistanceBalls
import Yau.Proofs.C02FlowRealRicci
import spec.CHAIN.LeafObligations

/-! The original local curvature-derivative estimate applies on actual
older buffered balls. A single profile bounds every covariant curvature
jet on every late newer unit ball with centre in the given compact set. -/

noncomputable section
open Set
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {X : KahlerManifold n}

theorem exists_uniform_flow_curvature_jet_bounds
    (hL23 : Yau.LeafObligations.L23)
    (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hC01 : HarnackCompleteness X o h)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∀ t : ℝ, 2 ≤ t → ∀ p ∈ K,
      ∀ j (x : Pt X), distFrom (h t) p x ≤ 1 → curvatureJetNorm (h t) j x ≤ C j := by
  obtain ⟨δ, hδ, hδone, hBall⟩ := exists_uniform_flow_ball_comparison
    o h U P ρ hloc hC01 K hK
  obtain ⟨B, hB, hCurv⟩ := curvatureJetNorm_zero_bound_on_compact_centered_balls
    o h U P ρ hloc hC01 K hK 4 (by norm_num)
  have hEst (j : ℕ) := hL23 n (manifold_dimension_pos X.manifold) j B 2 (δ / 2) 1
    hB (by norm_num) (by positivity) (by norm_num)
  choose C hC hBounds using hEst
  refine ⟨C, hC, ?_⟩
  intro t ht p hp j x hx
  let a := t - δ
  have ha : 1 ≤ a := by dsimp only [a]; linarith
  have ha0 : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 1).trans ha
  let gA := completeFlowSlice X o h hloc.1 hC01 a (by linarith)
  have hO : IsOpen (distBall (h a) p (2 * 2)) := isOpen_distBall gA p _
  have hOc : IsCompact (closure (distBall (h a) p (2 * 2))) :=
    isCompact_closure_distBall gA p _ (by norm_num)
  have hRF := localRealRicciFlow_on_slab X.metric.form h hloc.1
    (distBall (h a) p (2 * 2)) a (a + 2 * (δ / 2)) ha0
  have hCylinder : ∀ y ∈ distBall (h a) p (2 * 2),
      ∀ s ∈ Icc a (a + 2 * (δ / 2)), curvatureJetNorm (h s) 0 y ≤ B := by
    intro y hy s hs
    have hs0 := ha0.trans hs.1
    have hOld : distFrom (h a) p y < 4 := by
      have hh := (L23Aux.mem_distBall_iff (h a) p y (by norm_num : (0 : ℝ) < 2 * 2)).mp hy
      norm_num at hh
      exact hh
    have hDist : distFrom (h s) p y ≤ distFrom (h a) p y :=
      inducedDistance_le_of_gMat_order (h s) (h a)
        (metricFamilySmooth_slice hloc.1.2.1 hs0)
        (metricFamilySmooth_slice hloc.1.2.1 ha0)
        (fun z => hC01.2.2.2.2.2.1 z a s ha0 hs.1) p y
    exact hCurv s (ha.trans hs.1) p hp y (hDist.trans hOld.le)
  have hxOld : x ∈ distBall (h a) p 2 :=
    (L23Aux.mem_distBall_iff (h a) p x (by norm_num)).mpr (hBall t ht p hp x hx)
  have htI : t ∈ Icc (a + δ / 2) (a + 2 * (δ / 2)) := by
    dsimp only [a]
    constructor <;> linarith
  exact hBounds j X.manifold h p a hO hOc hRF hCylinder x hxOld t htI

end Yau.Blueprint.C02Proof
