import Yau.Proofs.C04RescaledTubeLocalBallComparison
import Yau.Proofs.C04BoundedGeometryChartsMetric
import Yau.LeafProofs.L23

/-! Original L23 on an earlier-time ball, followed by the proved local ball
comparison to the ball of the actual observation-time metric. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter
namespace Yau.Proofs.C04RescaledTubeAux
open Yau Blueprint LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem isCompact_closure_distBall (k : HermitianField M) (hs : MetricSmooth k)
    (hk : KahlerClosed k) (hc : IsCompleteDistance (lengthDist k))
    (p : M.Carrier) {r : ℝ} (hr : 0 < r) : IsCompact (closure (distBall k p r)) := by
  let g := C04ChartsAux.smoothMetric_of_complete_field k hs hk hc
  have hcompact := L12Aux.isCompact_inducedDistance_sublevel g p r
  change IsCompact {x : M.Carrier | inducedDistance k p x ≤ r} at hcompact
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · intro x hx
    exact ((L23Aux.mem_distBall_iff k p x hr).1 hx).le
  · exact isClosed_le (L23Aux.continuous_distFrom k hs p) continuous_const

theorem local_real_flow_mono (g : ℝ → HermitianField M) {O O' : Set M.Carrier}
    {I I' : Set ℝ} {σ : ℝ} (hflow : LocalRealRicciFlow g O I σ)
    (hO : O' ⊆ O) (hI : I' ⊆ I) : LocalRealRicciFlow g O' I' σ := by
  refine ⟨?_, ?_⟩
  · intro x a b
    exact (hflow.1 x a b).mono (fun p hp => ⟨hp.1, hI hp.2⟩)
  · intro x hx t ht a b
    exact (hflow.2 x (hO hx) t (hI ht) a b).mono hI

theorem uniform_current_ball_jets (n : ℕ) (hn : 0 < n)
    (θ r K Λ : ℝ) (hθ : 0 < θ) (hr : 0 < r) (hK : 0 < K) (hΛ : 1 ≤ Λ) :
    ∃ β : ℝ, 0 < β ∧ ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (M : ComplexManifold n) (g : ℝ → HermitianField M) (o : M.Carrier),
        LocalRealRicciFlow g Set.univ (Set.Icc (-2 * θ) (2 * θ)) 1 →
        (∀ t ∈ Set.Icc (-2 * θ) (2 * θ), KahlerClosed (g t)) →
        (∀ t ∈ Set.Icc (-2 * θ) (2 * θ), IsCompleteDistance (lengthDist (g t))) →
        (∀ x ∈ distBall (g 0) o (r + 2), ∀ t ∈ Set.Icc (-2 * θ) (2 * θ),
          curvatureJetNorm (g t) 0 x ≤ K) →
        (∀ x ∈ distBall (g 0) o (r + 2), ∀ u ∈ Set.Icc (-2 * θ) (2 * θ),
          ∀ v ∈ Set.Icc (-2 * θ) (2 * θ),
            HermLE (gMat (g u) x) (((Λ ^ 2 : ℝ) : ℂ) • gMat (g v) x)) →
        ∀ p ∈ distBall (g 0) o r, ∀ z : ℝ, |z| < θ →
          ∀ m : ℕ, ∀ x ∈ distBall (g z) p (2 * β), curvatureJetNorm (g z) m x ≤ C m := by
  have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ
  let b := 1 / (8 * Λ)
  let β := b / (4 * Λ)
  have hb : 0 < b := by dsimp [b]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  have hsqrt : Real.sqrt (Λ ^ 2) = Λ := Real.sqrt_sq hΛpos.le
  have htrap : Real.sqrt (Λ ^ 2) * (2 * b) < 1 := by
    rw [hsqrt]
    dsimp only [b]
    have he : Λ * (2 * (1 / (8 * Λ))) = 1 / 4 := by field_simp <;> ring
    rw [he]
    norm_num
  have hbupper : b ≤ 1 / 8 := by
    dsimp only [b]
    apply div_le_div_of_nonneg_left zero_le_one (by norm_num)
    nlinarith
  have hcurrrad : Real.sqrt (Λ ^ 2) * (2 * β) = b / 2 := by
    rw [hsqrt]
    dsimp only [β]
    field_simp
    <;> ring
  have htrapcurrent : Real.sqrt (Λ ^ 2) * (2 * β) < 1 := by rw [hcurrrad]; linarith
  choose C hC hL23 using fun m : ℕ =>
    (L23 n hn m K b (θ / 2) 1 hK hb (by positivity) zero_lt_one)
  refine ⟨β, hβ, C, hC, ?_⟩
  intro M g o hflow hkahler hcomplete hcurv hcmp p hp z hz m x hx
  let I := Set.Icc (-2 * θ) (2 * θ)
  let a := z - θ / 2
  have hzabs := abs_lt.1 hz
  have hzero : (0 : ℝ) ∈ I := ⟨by linarith, by linarith⟩
  have hzI : z ∈ I := ⟨by linarith [hzabs.1], by linarith [hzabs.2]⟩
  have haI : a ∈ I := ⟨by dsimp [a]; linarith [hzabs.1], by dsimp [a]; linarith [hzabs.2]⟩
  have hcyl : Set.Icc a (a + 2 * (θ / 2)) ⊆ I := by
    intro t ht
    constructor <;> dsimp only [a] at ht <;> linarith [hzabs.1, hzabs.2, ht.1, ht.2]
  have hs (t : ℝ) (ht : t ∈ I) : MetricSmooth (g t) :=
    L23Aux.metricFamilySmooth_slice g hflow.1 ht
  have hO : distBall (g a) p (2 * b) ⊆ distBall (g 0) o (r + 2) := by
    intro y hy
    have htrapball := central_ball_first_exit (g 0) (g a) (hs 0 hzero) (hs a haI)
      o p hr (by positivity : 0 < 2 * b) (by positivity : 0 < Λ ^ 2)
      htrap hp (fun y hy => hcmp y hy 0 hzero a haI) hy
    have hh := (L23Aux.mem_distBall_iff _ o y (by linarith : 0 < r + 1)).1 htrapball
    apply (L23Aux.mem_distBall_iff _ o y (by linarith : 0 < r + 2)).2
    linarith
  have hxearly : x ∈ distBall (g a) p b := by
    have hball := local_ball_comparison (g 0) (g z) (g a)
      (hs 0 hzero) (hs z hzI) (hs a haI) o p hr (by positivity : 0 < 2 * β)
      (by positivity : 0 < Λ ^ 2) (by positivity : 0 < Λ ^ 2)
      htrapcurrent hp (fun y hy => hcmp y hy 0 hzero z hzI)
      (fun y hy => hcmp y hy a haI z hzI) hx
    rw [hcurrrad] at hball
    have hh := (L23Aux.mem_distBall_iff _ p x (by positivity : 0 < b / 2)).1 hball
    apply (L23Aux.mem_distBall_iff _ p x hb).2
    linarith
  have hlocalflow := local_real_flow_mono g (O' := distBall (g a) p (2 * b))
    (I' := Set.Icc a (a + 2 * (θ / 2))) hflow (Set.subset_univ _) hcyl
  have hcompact := isCompact_closure_distBall (g a) (hs a haI)
    (hkahler a haI) (hcomplete a haI) p (by positivity : 0 < 2 * b)
  have hjet := hL23 m M g p a (L23Aux.isOpen_distBall (g a) (hs a haI) p _)
    hcompact hlocalflow (fun y hy t ht => hcurv y (hO hy) t (hcyl ht)) x hxearly z
    (show z ∈ Set.Icc (a + θ / 2) (a + 2 * (θ / 2)) by
      constructor <;> dsimp only [a] <;> linarith)
  exact hjet

end Yau.Proofs.C04RescaledTubeAux
