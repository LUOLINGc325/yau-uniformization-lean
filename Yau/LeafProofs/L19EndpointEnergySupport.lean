import Yau.LeafProofs.L19EndpointEnergyScalarSupport
import Yau.LeafProofs.L19EndpointEnergyMidpoint

/-! Actual local C2 upper supports for the original project distance
square, constructed from genuine minimizing midpoint branches. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- A concrete local support, with its actual C2 regularity and physical
first- and second-order bounds. -/
def RealDistanceSquareUpperSupport (g : SmoothMetric M) (x q : M.Carrier) : Prop :=
  letI := underlyingRealTangentNormedAddCommGroup g.form q
  letI := underlyingRealTangentInnerProductSpace g.form q
  ∃ F : M.Carrier → ℝ,
    ∃ b : OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) q),
    ContDiffAt ℝ 2 (F ∘ chartInv q) (chartPt q q) ∧
    F q = inducedDistance g.form x q ^ 2 ∧
    (∀ᶠ y in 𝓝 q, inducedDistance g.form x y ^ 2 ≤ F y) ∧
    endpointFrameGradientSq q b (F ∘ chartInv q) (chartPt q q) =
      4 * inducedDistance g.form x q ^ 2 ∧
    endpointFrameHessianTrace g q b (F ∘ chartInv q) (chartPt q q) ≤ 4 * (2 * n : ℕ)

/-- Away from the distance center, the actual midpoint energy and the
positive square-root profile produce a genuine C2 upper support. -/
theorem realDistanceSquareUpperSupport_of_ne
    (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ z, (ricci g.form z).PosSemidef) (x q : M.Carrier) (hxq : x ≠ q) :
    RealDistanceSquareUpperSupport g x q := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  obtain ⟨p, hpn, hpq, hfirst, hlast, O, hO, hz, Q, hQ, hQp, hends⟩ :=
    exists_realMinimizingMidpointBranch g x q
  subst q
  let q := (realGeodesicFlow g p (1 / 2)).proj
  let z := chartPt q q
  let r := inducedDistance g.form x q
  let a := r / 2
  let e : ComplexVector n → ℝ := fun y =>
    2 * (1 / 2) * realSegmentEnergy g (1 / 2) (Q y)
  let eM : M.Carrier → ℝ := fun y => e (chartPt q y)
  let F : M.Carrier → ℝ := endpointDistanceSquareProfile a ∘ eM
  let b := realGlobalParallelFrame g p (1 / 2)
  have hr : 0 < r := lt_of_le_of_ne (g.induced_distance_nonneg _ _)
    (Ne.symm (fun h => hxq (g.induced_distance_eq_zero.mp h)))
  have ha : 0 < a := by dsimp only [a]; positivity
  have htarget : z ∈ chartTarget q := mem_extChartAt_target q
  have he : ContDiffAt ℝ 2 e z := contDiffAt_const.mul
    (realSegmentEnergy_endpoint_contDiffAt_two g (1 / 2) p.proj q Q O hO z hz htarget hQ hends)
  have hez : e z = a ^ 2 := by
    dsimp only [e, a, r]
    rw [hQp, realSegmentEnergy, realTangentEnergy_eq_norm_sq, hpn]
    ring
  have hg : endpointFrameGradientSq q b e z = 4 * a ^ 2 := by
    have h := realEndpointEnergy_frameGradientSq g p (1 / 2) Q O hO z hz htarget hQ hQp hends b
    rw [realTangentEnergy_eq_norm_sq, hpn] at h
    convert h using 1 <;> dsimp only [a, r] <;> ring
  have ht : endpointFrameHessianTrace g q b e z ≤ 2 * (2 * n : ℕ) := by
    apply realEndpointEnergy_frameHessianTrace_le g hK hR p (by norm_num) Q O hO z hz htarget hQ hQp hends
    rw [hpn, hlast]
    ring
  obtain ⟨hC2, hval, hgrad, htrace⟩ :=
    endpointDistanceSquareProfile_support_bounds g q b ha he hez hg ht
  have heq : (F ∘ chartInv q) =ᶠ[𝓝 z] (endpointDistanceSquareProfile a ∘ e) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) q).mem_nhds htarget] with y hy
    change endpointDistanceSquareProfile a (e (chartPt q (chartInv q y))) = _
    have hr : chartPt q (chartInv q y) = y := (extChartAt (ComplexModel n) q).right_inv hy
    rw [hr]
    rfl
  have hInv : chartInv q z = q := (extChartAt (ComplexModel n) q).left_inv (mem_extChartAt_source q)
  simp only [Function.comp_apply] at hval
  have hFq : F q = r ^ 2 := by
    have h := heq.eq_of_nhds
    simp only [Function.comp_apply, hInv] at h
    rw [h, hval]
    dsimp only [a]
    ring
  have hupper : ∀ᶠ y in 𝓝 q, inducedDistance g.form x y ^ 2 ≤ F y := by
    have hchart : ContinuousAt (chartPt q) q :=
      (contMDiffAt_extChartAt (I := 𝓘(ℝ, ComplexVector n)) (n := 1)).continuousAt
    filter_upwards [(chartAt (ComplexVector n) q).open_source.mem_nhds (mem_chart_source _ _),
      hchart.preimage_mem_nhds (hO.mem_nhds hz)] with y hys hyO
    have hyInv : chartInv q (chartPt q y) = y :=
      (extChartAt (ComplexModel n) q).left_inv (by simpa only [extChartAt_source] using hys)
    have hpath := realSegmentEnergy_distance_sq_le g (Q (chartPt q y)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
    rw [(hends _ hyO).1, (hends _ hyO).2, hyInv] at hpath
    change inducedDistance g.form p.proj y ^ 2 ≤ eM y at hpath
    have hen : 0 ≤ eM y := (sq_nonneg _).trans hpath
    have hdist : inducedDistance g.form p.proj y ≤ Real.sqrt (eM y) := by
      have hs := Real.sq_sqrt hen
      nlinarith [g.induced_distance_nonneg p.proj y, Real.sqrt_nonneg (eM y)]
    have htri := g.induced_distance_triangle x p.proj y
    have hlen : inducedDistance g.form x y ≤ a + Real.sqrt (eM y) := by
      change inducedDistance g.form x p.proj = a at hfirst
      rw [hfirst] at htri
      linarith
    change inducedDistance g.form x y ^ 2 ≤ endpointDistanceSquareProfile a (eM y)
    rw [endpointDistanceSquareProfile_eq hen]
    exact (sq_le_sq₀ (g.induced_distance_nonneg _ _) (by positivity)).mpr hlen
  refine ⟨F, b, hC2.congr_of_eventuallyEq heq, hFq, hupper, ?_, ?_⟩
  · rw [endpointFrameGradientSq, heq.fderiv_eq]
    change endpointFrameGradientSq q b (endpointDistanceSquareProfile a ∘ e) z = _
    rw [hgrad]
    dsimp only [a, r]
    ring
  · rw [endpointFrameHessianTrace, (heq.fderiv (𝕜 := ℝ)).fderiv_eq, heq.fderiv_eq]
    exact htrace

/-- At the distance center the same actual branch energy itself is a C2
upper support; the zero-length midpoint has the original center as base. -/
theorem realDistanceSquareUpperSupport_at_center
    (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ z, (ricci g.form z).PosSemidef) (x : M.Carrier) :
    RealDistanceSquareUpperSupport g x x := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  obtain ⟨p, hpn, hpq, hfirst, hlast, O, hO, hz, Q, hQ, hQp, hends⟩ :=
    exists_realMinimizingMidpointBranch g x x
  have hdxx : inducedDistance g.form x x = 0 := g.induced_distance_eq_zero.mpr rfl
  rw [hdxx] at hpn hfirst hlast
  have hbase : p.proj = x := (g.induced_distance_eq_zero.mp (by simpa using hfirst)).symm
  let q := (realGeodesicFlow g p (1 / 2)).proj
  let z := chartPt q q
  let e : ComplexVector n → ℝ := fun y =>
    2 * (1 / 2) * realSegmentEnergy g (1 / 2) (Q y)
  let F : M.Carrier → ℝ := fun y => e (chartPt q y)
  let b := realGlobalParallelFrame g p (1 / 2)
  have htarget : z ∈ chartTarget q := mem_extChartAt_target q
  have he : ContDiffAt ℝ 2 e z := contDiffAt_const.mul
    (realSegmentEnergy_endpoint_contDiffAt_two g (1 / 2) p.proj q Q O hO z hz htarget hQ hends)
  have hez : e z = 0 := by
    dsimp only [e]
    rw [hQp, realSegmentEnergy, realTangentEnergy_eq_norm_sq, hpn]
    ring
  have hg : endpointFrameGradientSq q b e z = 0 := by
    have h := realEndpointEnergy_frameGradientSq g p (1 / 2) Q O hO z hz htarget hQ hQp hends b
    rw [realTangentEnergy_eq_norm_sq, hpn] at h
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using h
  have ht : endpointFrameHessianTrace g q b e z ≤ 2 * (2 * n : ℕ) := by
    apply realEndpointEnergy_frameHessianTrace_le g hK hR p (by norm_num) Q O hO z hz htarget hQ hQp hends
    rw [hpq, hpn, hlast]
    ring
  have heq : (F ∘ chartInv q) =ᶠ[𝓝 z] e := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) q).mem_nhds htarget] with y hy
    change e (chartPt q (chartInv q y)) = e y
    have hr : chartPt q (chartInv q y) = y := (extChartAt (ComplexModel n) q).right_inv hy
    rw [hr]
  have hupper : ∀ᶠ y in 𝓝 q, inducedDistance g.form q y ^ 2 ≤ F y := by
    have hchart : ContinuousAt (chartPt q) q :=
      (contMDiffAt_extChartAt (I := 𝓘(ℝ, ComplexVector n)) (n := 1)).continuousAt
    filter_upwards [(chartAt (ComplexVector n) q).open_source.mem_nhds (mem_chart_source _ _),
      hchart.preimage_mem_nhds (hO.mem_nhds hz)] with y hys hyO
    have hyInv : chartInv q (chartPt q y) = y :=
      (extChartAt (ComplexModel n) q).left_inv (by simpa only [extChartAt_source] using hys)
    have hpath := realSegmentEnergy_distance_sq_le g (Q (chartPt q y)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
    rw [(hends _ hyO).1, (hends _ hyO).2, hyInv, hbase, ← hpq] at hpath
    exact hpath
  have hresult : RealDistanceSquareUpperSupport g q q := by
    refine ⟨F, b, he.congr_of_eventuallyEq heq, ?_, hupper, ?_, ?_⟩
    · change e z = _
      rw [hez, g.induced_distance_eq_zero.mpr rfl]
      ring
    · rw [endpointFrameGradientSq, heq.fderiv_eq]
      change endpointFrameGradientSq q b e z = _
      rw [hg, g.induced_distance_eq_zero.mpr rfl]
      ring
    · rw [endpointFrameHessianTrace, (heq.fderiv (𝕜 := ℝ)).fderiv_eq, heq.fderiv_eq]
      exact ht.trans (by
        have hn : (0 : ℝ) ≤ (2 * n : ℕ) := Nat.cast_nonneg _
        linarith)
  exact hpq ▸ hresult

/-- Every original distance-square function has a concrete local C2 upper
support with the required physical gradient and Laplacian bounds. -/
theorem exists_realDistanceSquareUpperSupport
    (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ z, (ricci g.form z).PosSemidef) (x q : M.Carrier) :
    RealDistanceSquareUpperSupport g x q := by
  by_cases hxq : x = q
  · subst q
    exact realDistanceSquareUpperSupport_at_center g hK hR x
  · exact realDistanceSquareUpperSupport_of_ne g hK hR x q hxq

end Yau.LeafProofs.L19Aux
