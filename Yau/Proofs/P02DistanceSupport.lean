import Yau.Proofs.P02ParallelCurvature
import Yau.Proofs.P02EndpointLevi
import Yau.Proofs.P02Geodesic
import Yau.Proofs.P02EnergyInequalities
import Yau.LeafProofs.L22LeviCalculus
import spec.CHAIN.CONTRACTS

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P02Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract L22Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- A uniform positive lower support for negative distance on a fixed physical
ball. Every geodesic, parallel frame and endpoint variation is constructed
inside the proof from the original metric. -/
theorem exists_uniform_distance_lower_support (X : KahlerManifold n)
    (o : Pt X) (R : ℝ) :
    ∃ ε L : ℝ, 0 < ε ∧ 0 < L ∧
      ∀ x : Pt X, inducedDistance X.metric.form o x ≤ R →
      ∀ q : Pt X, L ≤ inducedDistance X.metric.form q x →
      ∃ s : Pt X → ℝ,
        ContDiffAt ℝ 2 (inChart x s) (chartPt x x) ∧
        s x = -inducedDistance X.metric.form q x ∧
        (∀ᶠ y in 𝓝 x, s y ≤ -inducedDistance X.metric.form q y) ∧
        ∀ w : ComplexVector n,
          ε * realMetricInChart X.metric.form x (chartPt x x) w w ≤
            complexLeviQuadratic (inChart x s) (chartPt x x) w := by
  letI := manifold_realSmooth X.manifold
  let h := X.metric.form
  have hs : MetricSmooth h := metricSmooth_of_smoothMetric X.metric
  have hk : KahlerClosed h := X.metric.kahler_equations
  let K : Set (Pt X) := {y | inducedDistance h o y ≤ R+1}
  have hK : IsCompact K := isCompact_inducedDistance_sublevel X.metric o (R+1)
  obtain ⟨κ,hκ,hbound⟩ := compact_bisectional_lower_bound X.metric
    X.positive_bisectional_curvature K hK
  let L := max 2 (16/κ)
  refine ⟨κ/32,L,by positivity,lt_of_lt_of_le (by norm_num : (0 : ℝ)<2) (le_max_left _ _),?_⟩
  intro x hx q hq
  let ell := inducedDistance h q x
  have hell2 : 2 ≤ ell := (le_max_left _ _).trans hq
  have hell : 0 < ell := by linarith
  have hellκ : 16/κ ≤ ell := (le_max_right _ _).trans hq
  obtain ⟨δ₀,hδ₀,γ,hγ0,hγ1,hγ₀,hspeed₀,htail⟩ :=
    exists_minimizing_fieldGeodesic X.metric q x
  obtain ⟨δ,e,P,A,hδsmall,H⟩ := exists_parallelVariationData h hs γ δ₀ hδ₀ hγ₀
  have hsub : Set.Ioo (-δ) (1+δ) ⊆ Set.Ioo (-δ₀) (1+δ₀) := by
    intro u hu
    constructor <;> linarith [hu.1,hu.2]
  have hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ)) :=
    ⟨hγ₀.1.mono hsub,fun c u hu hc => hγ₀.2 c u (hsub hu) hc⟩
  have hunit : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-δ) (1+δ) := by
    intro u hu
    constructor <;> linarith [hu.1,hu.2,H.delta_pos]
  have hspeed : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      actualSpeedSq h γ u = inducedDistance h (γ 0) (γ 1)^2 := by
    intro u hu
    simpa only [hγ0,hγ1] using hspeed₀ u hu
  let E := endpointEnergy h e A
  have HE := endpointEnergy_majorant h hs γ δ e P A H hγ hspeed
  have hE : ContDiffAt ℝ 2 (inChart x E) (chartPt x x) := by
    simpa only [hγ1] using HE.1
  let s : Pt X → ℝ := fun y => -(ell^2+E y)/(2*ell)
  have hsc : ContDiffAt ℝ 2 (inChart x s) (chartPt x x) := by
    exact ((contDiffAt_const.add hE).neg).div_const _
  refine ⟨s,hsc,?_,?_,?_⟩
  · have hEx : E x = ell^2 := by simpa only [hγ0,hγ1] using HE.2.1
    change -(ell^2+E x)/(2*ell) = -ell
    rw [hEx]
    field_simp
    <;> ring
  · have hxTarget : x ∈ e.target := by
      rw [← hγ1, ← H.endpoint_zero]
      exact e.map_source H.zero_source
    filter_upwards [e.open_target.mem_nhds hxTarget] with y hy
    have Hmaj := HE.2.2 y hy
    rw [hγ0] at Hmaj
    have Hd := energy_affine_distance_majorant ell (inducedDistance h q y) (E y) hell Hmaj
    change -(ell^2+E y)/(2*ell) ≤ -inducedDistance h q y
    simpa only [neg_div] using neg_le_neg Hd
  · intro w
    let Q := realMetricInChart h x (chartPt x x) w w
    have hQ : 0 ≤ Q := realMetricInChart_quadratic_nonneg h x (chartPt x x) w
    have hBcont : ContinuousOn (parallelBisectional h γ P w) (Set.Icc (0 : ℝ) 1) :=
      (parallelBisectional_continuousOn h hs γ δ e P A H hγ w).mono hunit
    have hBnonneg : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 ≤ parallelBisectional h γ P w u :=
      fun u hu => parallelBisectional_nonneg h hs X.positive_bisectional_curvature
        γ δ hγ P w u (hunit hu)
    have hterminal : ∀ u ∈ Set.Icc (1-1/ell) 1,
        κ*ell^2*Q ≤ parallelBisectional h γ P w u := by
      intro u hu
      have hinv : 1/ell ≤ (1/2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hell2
      have huunit : u ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hu.1],hu.2⟩
      have hdist : inducedDistance h (γ u) x ≤ 1 := by
        have HH := htail u huunit
        have hmul : (1-u)*ell ≤ 1 := by
          have HH' := mul_le_mul_of_nonneg_right hu.1 hell.le
          have hcancel : (1-1/ell)*ell = ell-1 := by field_simp
          rw [hcancel] at HH'
          linarith
        exact HH.trans hmul
      have hyK : γ u ∈ K := by
        have Htri := X.metric.induced_distance_triangle o x (γ u)
        have Hsym := X.metric.induced_distance_symm x (γ u)
        change inducedDistance h o (γ u) ≤ R+1
        rw [Hsym] at Htri
        linarith
      have HB := hbound (γ u) hyK (realCurveVelocity γ u) (P u w)
      change κ*actualSpeedSq h γ u *
        (underlyingRealRiemannianMetric h).inner (γ u) (P u w) (P u w) ≤ _ at HB
      rw [hspeed₀ u huunit,H.pairing u (hunit huunit) w w,hγ1] at HB
      rw [parallelBisectional_eq_transport h hs γ δ hγ P w u (hunit huunit)]
      exact HB
    have Hint := terminal_curvature_integral_lower (parallelBisectional h γ P w)
      κ ell Q hκ hell2 hQ hBcont hBnonneg hterminal
    have Hsmall := normalized_energy_trace_bound κ ell Q
      (∫ u in Set.Icc (0 : ℝ) 1, u^2*parallelBisectional h γ P w u)
      hκ hell hQ hellκ Hint
    have Hlevi := endpointEnergy_levi_eq h hs hk γ δ e P A H hγ hspeed w
    rw [hγ1] at Hlevi
    have hfun : inChart x s = fun z => (-1/(2*ell))*(ell^2+inChart x E z) := by
      funext z
      change -(ell^2+E (chartInv x z))/(2*ell) =
        (-1/(2*ell))*(ell^2+E (chartInv x z))
      ring
    rw [hfun, complexLeviQuadratic_const_mul (contDiffAt_const.add hE),
      complexLeviQuadratic_add contDiffAt_const hE]
    have hconst : complexLeviQuadratic (fun _ : ComplexVector n => ell^2)
        (chartPt x x) w = 0 := by simp [complexLeviQuadratic]
    rw [hconst,zero_add]
    have Hsmall' := (div_le_iff₀ (show 0 < 2*ell by positivity)).mp Hsmall
    have Hratio : (-1/(2*ell))*complexLeviQuadratic (inChart x E) (chartPt x x) w =
        -complexLeviQuadratic (inChart x E) (chartPt x x) w/(2*ell) := by ring
    rw [Hratio]
    apply (le_div_iff₀ (show 0 < 2*ell by positivity)).mpr
    change κ/32*Q*(2*ell) ≤ _
    nlinarith [Hlevi]

end Yau.NodeProofs.P02Aux
