import Yau.LeafProofs.L19GaussianWeight

/-! Moving the endpoint-energy anchor toward the Gaussian center sharpens
the local radial Laplacian constant. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- An actual minimizing endpoint branch based at any interior fraction of
the original geodesic, including fractions arbitrarily close to zero. -/
theorem exists_realMinimizingInteriorBranch (g : SmoothMetric M)
    (x y : M.Carrier) {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI : ∀ a : M.Carrier, NormedAddCommGroup
      (TangentSpace 𝓘(ℝ, ComplexVector n) a) :=
      fun a => underlyingRealTangentNormedAddCommGroup g.form a
    letI : ∀ a : M.Carrier, InnerProductSpace ℝ
      (TangentSpace 𝓘(ℝ, ComplexVector n) a) :=
      fun a => underlyingRealTangentInnerProductSpace g.form a
    ∃ p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier,
      ‖p.2‖ = inducedDistance g.form x y ∧
      (realGeodesicFlow g p (1 - s)).proj = y ∧
      inducedDistance g.form x p.proj = s * inducedDistance g.form x y ∧
      inducedDistance g.form p.proj y = (1 - s) * inducedDistance g.form x y ∧
      ∃ O : Set (ComplexVector n), IsOpen O ∧
        chartPt (realGeodesicFlow g p (1 - s)).proj
          (realGeodesicFlow g p (1 - s)).proj ∈ O ∧
        ∃ Q : ComplexVector n → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier,
          ContMDiffOn 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1 Q O ∧
          Q (chartPt (realGeodesicFlow g p (1 - s)).proj
            (realGeodesicFlow g p (1 - s)).proj) = p ∧
          (∀ z ∈ O, (Q z).proj = p.proj ∧
            (realGeodesicFlow g (Q z) (1 - s)).proj =
              chartInv (realGeodesicFlow g p (1 - s)).proj z) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ a : M.Carrier, NormedAddCommGroup
      (TangentSpace 𝓘(ℝ, ComplexVector n) a) :=
    fun a => underlyingRealTangentNormedAddCommGroup g.form a
  letI : ∀ a : M.Carrier, InnerProductSpace ℝ
      (TangentSpace 𝓘(ℝ, ComplexVector n) a) :=
    fun a => underlyingRealTangentInnerProductSpace g.form a
  let d : ℝ := 1 - s
  have hd0 : 0 < d := sub_pos.mpr hs.2
  have hd1 : d < 1 := by dsimp [d]; linarith [hs.1]
  obtain ⟨v, hv, hnv⟩ := exists_minimizing_realExponential g x y
  let p₀ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨x, v⟩
  let p := realGeodesicFlow g p₀ s
  let pR := realSegmentReverse g 1 p₀
  have hfull : (realGeodesicFlow g p₀ 1).proj = y := hv
  have hmin : inducedDistance g.form p₀.proj
      (realGeodesicFlow g p₀ 1).proj = 1 * ‖p₀.2‖ := by
    rw [hfull, one_mul]
    exact hnv.symm
  have hpn : ‖p.2‖ = inducedDistance g.form x y := by
    rw [realGeodesicFlow_velocity_norm]
    exact hnv
  have htail : (realGeodesicFlow g p d).proj = y := by
    dsimp only [p]
    rw [← realGeodesicFlow_add]
    convert hfull using 2 <;> dsimp [d] <;> ring
  have hRbase : pR.proj = y := hfull
  have hRend : (realGeodesicFlow g pR 1).proj = x := by
    rw [realSegmentReverse_terminal]
    rfl
  have hRE := realSegmentEnergy_reverse g 1 p₀
  dsimp only [realSegmentEnergy] at hRE
  have hRE' : realTangentEnergy g.form pR = realTangentEnergy g.form p₀ := by
    linarith
  rw [realTangentEnergy_eq_norm_sq, realTangentEnergy_eq_norm_sq] at hRE'
  have hRn : ‖pR.2‖ = inducedDistance g.form x y := by
    nlinarith [norm_nonneg pR.2, norm_nonneg p₀.2]
  have hRmin : inducedDistance g.form pR.proj
      (realGeodesicFlow g pR 1).proj = 1 * ‖pR.2‖ := by
    rw [hRn, one_mul, hRbase, hRend]
    exact g.induced_distance_symm _ _
  have hrev : realSegmentReverse g d p = pR := by
    dsimp only [realSegmentReverse, p, pR]
    rw [← realGeodesicFlow_add]
    congr 1
    dsimp [d]
    ring
  have hdet : (realGeodesicJacobiMatrix g
      (realSegmentReverse g d p) d).det ≠ 0 := by
    rw [hrev]
    exact realGeodesicJacobiMatrix_det_ne_zero_of_minimizing g pR
      (by norm_num) hRmin d ⟨hd0, hd1⟩
  obtain ⟨U, hU, hpU, P, hP, hPp, hPends, _⟩ :=
    exists_realGeodesic_endpointBranch_reversed g p d hdet
  have hfirst := realGeodesicFlow_dist_eq_of_minimizing g p₀ 1 hmin s
    ⟨hs.1.le, hs.2.le⟩
  have hfirst' : inducedDistance g.form x p.proj =
      s * inducedDistance g.form x y := by
    rw [hnv] at hfirst
    exact hfirst
  have hlast : inducedDistance g.form p.proj y =
      d * inducedDistance g.form x y := by
    have hu := realGeodesicFlow_distFrom_le g p d
    rw [htail, realTangentEnergy_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg p.2), hpn] at hu
    change inducedDistance g.form p.proj y ≤
      inducedDistance g.form x y * |d| at hu
    rw [abs_of_pos hd0] at hu
    have htri := g.induced_distance_triangle x p.proj y
    rw [hfirst'] at htri
    dsimp [d] at hu ⊢
    linarith
  exact ⟨p, hpn, htail, hfirst', hlast,
    exists_realEndpointChartBranch g p d U hU hpU P hP hPp hPends⟩

private theorem profile_secondDeriv_at_sq {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) :
    deriv (deriv (endpointDistanceSquareProfile a)) (b ^ 2) =
      -(a / (2 * b ^ 3)) := by
  have hs : HasDerivAt Real.sqrt (1 / (2 * b)) (b ^ 2) := by
    simpa only [Real.sqrt_sq hb.le] using
      Real.hasDerivAt_sqrt (sq_pos_of_pos hb).ne'
  have hL := ((hasDerivAt_const (b ^ 2) a).div hs
    (by simpa only [Real.sqrt_sq hb.le] using hb.ne')).add_const 1
  have heq : deriv (endpointDistanceSquareProfile a) =ᶠ[𝓝 (b ^ 2)]
      (fun x => a / Real.sqrt x + 1) := by
    filter_upwards [Ioi_mem_nhds (sq_pos_of_pos hb)] with x hx
    exact (endpointDistanceSquareProfile_hasDerivAt hx).deriv
  simp only [Pi.div_apply] at hL
  rw [heq.deriv_eq, hL.deriv, Real.sqrt_sq hb.le]
  field_simp
  ring

private theorem profile_deriv_at_sq {a b : ℝ} (hb : 0 < b) :
    deriv (endpointDistanceSquareProfile a) (b ^ 2) = a / b + 1 := by
  rw [(endpointDistanceSquareProfile_hasDerivAt (sq_pos_of_pos hb)).deriv,
    Real.sqrt_sq hb.le]

/-- The shifted center gives a C² upper support whose physical trace tends
to the sharp Euclidean value `2m` as the shift fraction tends to zero. -/
theorem exists_realDistanceSquareUpperSupport_interior
    (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ z, (ricci g.form z).PosSemidef)
    (o q : M.Carrier) (hoq : o ≠ q) {s : ℝ}
    (hs : s ∈ Set.Ioo 0 1) :
    letI := underlyingRealTangentNormedAddCommGroup g.form q
    letI := underlyingRealTangentInnerProductSpace g.form q
    ∃ F : M.Carrier → ℝ,
      ∃ basis : OrthonormalBasis (Fin (2 * n)) ℝ
        (TangentSpace 𝓘(ℝ, ComplexVector n) q),
        ContDiffAt ℝ 2 (F ∘ chartInv q) (chartPt q q) ∧
        F q = inducedDistance g.form o q ^ 2 ∧
        (∀ᶠ y in 𝓝 q, inducedDistance g.form o y ^ 2 ≤ F y) ∧
        endpointFrameHessianTrace g q basis (F ∘ chartInv q) (chartPt q q) ≤
          2 * (2 * n : ℕ) / (1 - s) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup
      (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ
      (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  obtain ⟨p, hpn, hpq, hfirst, hlast, O, hO, hz, Q, hQ, hQp, hends⟩ :=
    exists_realMinimizingInteriorBranch g o q hs
  subst q
  let q := (realGeodesicFlow g p (1 - s)).proj
  let z := chartPt q q
  let r := inducedDistance g.form o q
  let d : ℝ := 1 - s
  let a := s * r
  let b := d * r
  let e : ComplexVector n → ℝ := fun y =>
    2 * d * realSegmentEnergy g d (Q y)
  let eM : M.Carrier → ℝ := fun y => e (chartPt q y)
  let F : M.Carrier → ℝ := fun y => endpointDistanceSquareProfile a (eM y)
  let basis := realGlobalParallelFrame g p d
  have hr : 0 < r := lt_of_le_of_ne (g.induced_distance_nonneg _ _)
    (Ne.symm (fun h => hoq (g.induced_distance_eq_zero.mp h)))
  have hd : 0 < d := sub_pos.mpr hs.2
  have ha : 0 < a := mul_pos hs.1 hr
  have hb : 0 < b := mul_pos hd hr
  have htarget : z ∈ chartTarget q := mem_extChartAt_target q
  have he : ContDiffAt ℝ 2 e z := contDiffAt_const.mul
    (realSegmentEnergy_endpoint_contDiffAt_two g d p.proj q Q O hO z hz htarget hQ hends)
  have hez : e z = b ^ 2 := by
    dsimp only [e, b, r]
    rw [hQp, realSegmentEnergy, realTangentEnergy_eq_norm_sq, hpn]
    ring
  have ht : endpointFrameHessianTrace g q basis e z ≤ 2 * (2 * n : ℕ) := by
    apply realEndpointEnergy_frameHessianTrace_le g hK hR p hd
      Q O hO z hz htarget hQ hQp hends
    rw [hpn, hlast]
  have hprofile : ContDiffAt ℝ 2 (endpointDistanceSquareProfile a) (e z) :=
    endpointDistanceSquareProfile_contDiffAt (hez ▸ (sq_pos_of_pos hb).ne')
  have hFe : ContDiffAt ℝ 2 (endpointDistanceSquareProfile a ∘ e) z :=
    hprofile.comp z he
  have hgrad0 : 0 ≤ endpointFrameGradientSq q basis e z := by
    unfold endpointFrameGradientSq
    positivity
  have htraceFe : endpointFrameHessianTrace g q basis
      (endpointDistanceSquareProfile a ∘ e) z ≤
      2 * (2 * n : ℕ) / d := by
    rw [endpointFrameHessianTrace_scalar_comp g q basis he hprofile,
      hez, profile_deriv_at_sq hb, profile_secondDeriv_at_sq ha.le hb]
    have hneg : -(a / (2 * b ^ 3)) * endpointFrameGradientSq q basis e z ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hgrad0
    have hcoef : a / b + 1 = 1 / d := by
      dsimp only [a, b, d]
      field_simp [show 1 - s ≠ 0 by linarith [hs.2]]
      ring
    rw [hcoef]
    have hc : 0 ≤ 1 / d := by positivity
    have hh := mul_le_mul_of_nonneg_left ht hc
    calc
      _ ≤ (1 / d) * endpointFrameHessianTrace g q basis e z := by linarith
      _ ≤ (1 / d) * (2 * (2 * n : ℕ)) := hh
      _ = _ := by ring
  have heq : (F ∘ chartInv q) =ᶠ[𝓝 z]
      (endpointDistanceSquareProfile a ∘ e) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) q).mem_nhds htarget]
      with y hy
    change endpointDistanceSquareProfile a (e (chartPt q (chartInv q y))) = _
    have hr : chartPt q (chartInv q y) = y :=
      (extChartAt (ComplexModel n) q).right_inv hy
    rw [hr]
    rfl
  have hInv : chartInv q z = q :=
    (extChartAt (ComplexModel n) q).left_inv (mem_extChartAt_source q)
  have hFq : F q = r ^ 2 := by
    change endpointDistanceSquareProfile a (e z) = _
    rw [hez, endpointDistanceSquareProfile_eq (sq_nonneg b), Real.sqrt_sq hb.le]
    dsimp only [a, b, d]
    ring
  have hupper : ∀ᶠ y in 𝓝 q, inducedDistance g.form o y ^ 2 ≤ F y := by
    have hchart : ContinuousAt (chartPt q) q :=
      (contMDiffAt_extChartAt (I := 𝓘(ℝ, ComplexVector n)) (n := 1)).continuousAt
    filter_upwards [(chartAt (ComplexVector n) q).open_source.mem_nhds
      (mem_chart_source _ _), hchart.preimage_mem_nhds (hO.mem_nhds hz)]
      with y hys hyO
    have hyInv : chartInv q (chartPt q y) = y :=
      (extChartAt (ComplexModel n) q).left_inv
        (by simpa only [extChartAt_source] using hys)
    have hpath := realSegmentEnergy_distance_sq_le g (Q (chartPt q y)) hd.le
    rw [(hends _ hyO).1, (hends _ hyO).2, hyInv] at hpath
    change inducedDistance g.form p.proj y ^ 2 ≤ eM y at hpath
    have hen : 0 ≤ eM y := (sq_nonneg _).trans hpath
    have hdist : inducedDistance g.form p.proj y ≤ Real.sqrt (eM y) := by
      have hs := Real.sq_sqrt hen
      nlinarith [g.induced_distance_nonneg p.proj y, Real.sqrt_nonneg (eM y)]
    have htri := g.induced_distance_triangle o p.proj y
    have hlen : inducedDistance g.form o y ≤ a + Real.sqrt (eM y) := by
      change inducedDistance g.form o p.proj = a at hfirst
      rw [hfirst] at htri
      linarith
    change inducedDistance g.form o y ^ 2 ≤ endpointDistanceSquareProfile a (eM y)
    rw [endpointDistanceSquareProfile_eq hen]
    exact (sq_le_sq₀ (g.induced_distance_nonneg _ _) (by positivity)).mpr hlen
  refine ⟨F, basis, hFe.congr_of_eventuallyEq heq, hFq, hupper, ?_⟩
  rw [endpointFrameHessianTrace,
    (heq.fderiv (𝕜 := ℝ)).fderiv_eq, heq.fderiv_eq]
  exact htraceFe

/-- The genuine Gaussian lower support has the sharp `2m` trace coefficient
in the limit as the anchor approaches the center. -/
theorem exists_gaussianLowerSupport_interior
    (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ z, (ricci g.form z).PosSemidef)
    (o q : M.Carrier) (hoq : o ≠ q) {s : ℝ}
    (hs : s ∈ Set.Ioo 0 1) {a : ℝ} (ha : 0 ≤ a) :
    letI := underlyingRealTangentNormedAddCommGroup g.form q
    letI := underlyingRealTangentInnerProductSpace g.form q
    ∃ S : M.Carrier → ℝ,
      ∃ basis : OrthonormalBasis (Fin (2 * n)) ℝ
        (TangentSpace 𝓘(ℝ, ComplexVector n) q),
        ContDiffAt ℝ 2 (S ∘ chartInv q) (chartPt q q) ∧
        S q = gaussianWeight g o a q ∧
        (∀ᶠ y in 𝓝 q, S y ≤ gaussianWeight g o a y) ∧
        -(2 * (2 * n : ℕ) * a / (1 - s)) * gaussianWeight g o a q ≤
          endpointFrameHessianTrace g q basis (S ∘ chartInv q) (chartPt q q) := by
  obtain ⟨F, basis, hF, hval, hupper, htrace⟩ :=
    exists_realDistanceSquareUpperSupport_interior g hK hR o q hoq hs
  let S : M.Carrier → ℝ := fun y => Real.exp (-(a * F y))
  let z := chartPt q q
  have hinv : chartInv q z = q :=
    (extChartAt (ComplexModel n) q).left_inv (mem_extChartAt_source q)
  have hprofile : ContDiffAt ℝ 2
      (fun t : ℝ => Real.exp (-(a * t))) ((F ∘ chartInv q) z) := by
    simpa only [Function.comp_apply, hinv] using gaussianProfile_contDiffAt a (F q)
  have hS : ContDiffAt ℝ 2 (S ∘ chartInv q) z := hprofile.comp z hF
  have hcontact : S q = gaussianWeight g o a q := by
    simp only [S, gaussianWeight, hval]
  have hlower : ∀ᶠ y in 𝓝 q, S y ≤ gaussianWeight g o a y := by
    filter_upwards [hupper] with y hy
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hy ha))
  have htraceS : endpointFrameHessianTrace g q basis (S ∘ chartInv q) z =
      (-a * gaussianWeight g o a q) *
        endpointFrameHessianTrace g q basis (F ∘ chartInv q) z +
      (a ^ 2 * gaussianWeight g o a q) *
        endpointFrameGradientSq q basis (F ∘ chartInv q) z := by
    change endpointFrameHessianTrace g q basis
      ((fun t : ℝ => Real.exp (-(a * t))) ∘ (F ∘ chartInv q)) z = _
    rw [endpointFrameHessianTrace_scalar_comp g q basis hF hprofile,
      Function.comp_apply, hinv, gaussianProfile_deriv,
      gaussianProfile_secondDeriv]
    dsimp only [z]
    simp only [gaussianWeight, hval]
  refine ⟨S, basis, hS, hcontact, hlower, ?_⟩
  rw [htraceS]
  have hW : 0 ≤ gaussianWeight g o a q := (gaussianWeight_pos g o a q).le
  have hneg : -a * gaussianWeight g o a q ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hW
  have hbase := mul_le_mul_of_nonpos_left htrace hneg
  have hquad : 0 ≤ (a ^ 2 * gaussianWeight g o a q) *
      endpointFrameGradientSq q basis (F ∘ chartInv q) z := by
    apply mul_nonneg (mul_nonneg (sq_nonneg _) hW)
    unfold endpointFrameGradientSq
    positivity
  dsimp only [z] at hbase hquad ⊢
  calc
    _ = (-a * gaussianWeight g o a q) *
        (2 * (2 * n : ℕ) / (1 - s)) := by ring
    _ ≤ (-a * gaussianWeight g o a q) *
        endpointFrameHessianTrace g q basis (F ∘ chartInv q) (chartPt q q) := hbase
    _ ≤ _ := by linarith

/-- At the distance center, the unshifted endpoint energy gives the exact
Euclidean `2m` trace bound. -/
theorem exists_realDistanceSquareUpperSupport_center_sharp
    (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ z, (ricci g.form z).PosSemidef) (o : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup g.form o
    letI := underlyingRealTangentInnerProductSpace g.form o
    ∃ F : M.Carrier → ℝ,
      ∃ basis : OrthonormalBasis (Fin (2 * n)) ℝ
        (TangentSpace 𝓘(ℝ, ComplexVector n) o),
        ContDiffAt ℝ 2 (F ∘ chartInv o) (chartPt o o) ∧
        F o = inducedDistance g.form o o ^ 2 ∧
        (∀ᶠ y in 𝓝 o, inducedDistance g.form o y ^ 2 ≤ F y) ∧
        endpointFrameHessianTrace g o basis (F ∘ chartInv o) (chartPt o o) ≤
          2 * (2 * n : ℕ) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup
      (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ
      (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  obtain ⟨p, hpn, hpq, hfirst, hlast, O, hO, hz, Q, hQ, hQp, hends⟩ :=
    exists_realMinimizingMidpointBranch g o o
  have hdxx : inducedDistance g.form o o = 0 :=
    g.induced_distance_eq_zero.mpr rfl
  rw [hdxx] at hpn hfirst hlast
  have hbase : p.proj = o :=
    (g.induced_distance_eq_zero.mp (by simpa using hfirst)).symm
  let q := (realGeodesicFlow g p (1 / 2)).proj
  let z := chartPt q q
  let e : ComplexVector n → ℝ := fun y =>
    2 * (1 / 2) * realSegmentEnergy g (1 / 2) (Q y)
  let F : M.Carrier → ℝ := fun y => e (chartPt q y)
  let basis := realGlobalParallelFrame g p (1 / 2)
  have htarget : z ∈ chartTarget q := mem_extChartAt_target q
  have he : ContDiffAt ℝ 2 e z := contDiffAt_const.mul
    (realSegmentEnergy_endpoint_contDiffAt_two g (1 / 2) p.proj q Q O hO z hz htarget hQ hends)
  have hez : e z = 0 := by
    dsimp only [e]
    rw [hQp, realSegmentEnergy, realTangentEnergy_eq_norm_sq, hpn]
    ring
  have ht : endpointFrameHessianTrace g q basis e z ≤ 2 * (2 * n : ℕ) := by
    apply realEndpointEnergy_frameHessianTrace_le g hK hR p
      (by norm_num) Q O hO z hz htarget hQ hQp hends
    rw [hpq, hpn, hlast]
    ring
  have heq : (F ∘ chartInv q) =ᶠ[𝓝 z] e := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) q).mem_nhds htarget]
      with y hy
    change e (chartPt q (chartInv q y)) = e y
    have hr : chartPt q (chartInv q y) = y :=
      (extChartAt (ComplexModel n) q).right_inv hy
    rw [hr]
  have hupper : ∀ᶠ y in 𝓝 q, inducedDistance g.form q y ^ 2 ≤ F y := by
    have hchart : ContinuousAt (chartPt q) q :=
      (contMDiffAt_extChartAt (I := 𝓘(ℝ, ComplexVector n)) (n := 1)).continuousAt
    filter_upwards [(chartAt (ComplexVector n) q).open_source.mem_nhds
      (mem_chart_source _ _), hchart.preimage_mem_nhds (hO.mem_nhds hz)]
      with y hys hyO
    have hyInv : chartInv q (chartPt q y) = y :=
      (extChartAt (ComplexModel n) q).left_inv
        (by simpa only [extChartAt_source] using hys)
    have hpath := realSegmentEnergy_distance_sq_le g (Q (chartPt q y))
      (by norm_num : 0 ≤ (1 / 2 : ℝ))
    rw [(hends _ hyO).1, (hends _ hyO).2, hyInv, hbase, ← hpq] at hpath
    exact hpath
  have hresult :
      ∃ F : M.Carrier → ℝ,
        ∃ basis : OrthonormalBasis (Fin (2 * n)) ℝ
          (TangentSpace 𝓘(ℝ, ComplexVector n) q),
          ContDiffAt ℝ 2 (F ∘ chartInv q) (chartPt q q) ∧
          F q = inducedDistance g.form q q ^ 2 ∧
          (∀ᶠ y in 𝓝 q, inducedDistance g.form q y ^ 2 ≤ F y) ∧
          endpointFrameHessianTrace g q basis (F ∘ chartInv q) (chartPt q q) ≤
            2 * (2 * n : ℕ) := by
    refine ⟨F, basis, he.congr_of_eventuallyEq heq, ?_, hupper, ?_⟩
    · change e z = _
      rw [hez, g.induced_distance_eq_zero.mpr rfl]
      ring
    · rw [endpointFrameHessianTrace,
        (heq.fderiv (𝕜 := ℝ)).fderiv_eq, heq.fderiv_eq]
      exact ht
  exact hpq ▸ hresult

/-- Sharp Gaussian local lower support at the center. -/
theorem exists_gaussianLowerSupport_center_sharp
    (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ z, (ricci g.form z).PosSemidef)
    (o : M.Carrier) {a : ℝ} (ha : 0 ≤ a) :
    letI := underlyingRealTangentNormedAddCommGroup g.form o
    letI := underlyingRealTangentInnerProductSpace g.form o
    ∃ S : M.Carrier → ℝ,
      ∃ basis : OrthonormalBasis (Fin (2 * n)) ℝ
        (TangentSpace 𝓘(ℝ, ComplexVector n) o),
        ContDiffAt ℝ 2 (S ∘ chartInv o) (chartPt o o) ∧
        S o = gaussianWeight g o a o ∧
        (∀ᶠ y in 𝓝 o, S y ≤ gaussianWeight g o a y) ∧
        -(2 * (2 * n : ℕ) * a) * gaussianWeight g o a o ≤
          endpointFrameHessianTrace g o basis (S ∘ chartInv o) (chartPt o o) := by
  obtain ⟨F, basis, hF, hval, hupper, htrace⟩ :=
    exists_realDistanceSquareUpperSupport_center_sharp g hK hR o
  let S : M.Carrier → ℝ := fun y => Real.exp (-(a * F y))
  let z := chartPt o o
  have hinv : chartInv o z = o :=
    (extChartAt (ComplexModel n) o).left_inv (mem_extChartAt_source o)
  have hprofile : ContDiffAt ℝ 2
      (fun t : ℝ => Real.exp (-(a * t))) ((F ∘ chartInv o) z) := by
    simpa only [Function.comp_apply, hinv] using gaussianProfile_contDiffAt a (F o)
  have hS : ContDiffAt ℝ 2 (S ∘ chartInv o) z := hprofile.comp z hF
  have hcontact : S o = gaussianWeight g o a o := by
    simp only [S, gaussianWeight, hval]
  have hlower : ∀ᶠ y in 𝓝 o, S y ≤ gaussianWeight g o a y := by
    filter_upwards [hupper] with y hy
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hy ha))
  have htraceS : endpointFrameHessianTrace g o basis (S ∘ chartInv o) z =
      (-a * gaussianWeight g o a o) *
        endpointFrameHessianTrace g o basis (F ∘ chartInv o) z +
      (a ^ 2 * gaussianWeight g o a o) *
        endpointFrameGradientSq o basis (F ∘ chartInv o) z := by
    change endpointFrameHessianTrace g o basis
      ((fun t : ℝ => Real.exp (-(a * t))) ∘ (F ∘ chartInv o)) z = _
    rw [endpointFrameHessianTrace_scalar_comp g o basis hF hprofile,
      Function.comp_apply, hinv, gaussianProfile_deriv,
      gaussianProfile_secondDeriv]
    dsimp only [z]
    simp only [gaussianWeight, hval]
  refine ⟨S, basis, hS, hcontact, hlower, ?_⟩
  rw [htraceS]
  have hW : 0 ≤ gaussianWeight g o a o := (gaussianWeight_pos g o a o).le
  have hneg : -a * gaussianWeight g o a o ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hW
  have hbase := mul_le_mul_of_nonpos_left htrace hneg
  have hquad : 0 ≤ (a ^ 2 * gaussianWeight g o a o) *
      endpointFrameGradientSq o basis (F ∘ chartInv o) z := by
    apply mul_nonneg (mul_nonneg (sq_nonneg _) hW)
    unfold endpointFrameGradientSq
    positivity
  dsimp only [z] at hbase hquad ⊢
  nlinarith

/-- A single interior fraction gives a global viscosity bound, with no
exception at the center or cut locus. -/
theorem gaussianWeight_hasPhysicalLowerSupports_fraction
    (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ z, (ricci g.form z).PosSemidef)
    (o : M.Carrier) {a : ℝ} (ha : 0 ≤ a)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 1) :
    HasPhysicalLowerSupports g (gaussianWeight g o a)
      (-((2 * n : ℕ) * a / (1 - s))) := by
  intro q
  by_cases hqo : q = o
  · subst q
    obtain ⟨S, basis, hS, hcontact, hlower, htrace⟩ :=
      exists_gaussianLowerSupport_center_sharp g hK hR o ha
    refine ⟨S, basis, hS, hcontact, hlower, ?_⟩
    have hd : 0 < 1 - s := sub_pos.mpr hs.2
    have hdle : 1 - s ≤ 1 := by linarith [hs.1]
    have hW : 0 ≤ gaussianWeight g o a o := (gaussianWeight_pos g o a o).le
    have hfac : 0 ≤ (2 * (2 * n : ℕ) * a) * gaussianWeight g o a o := by
      positivity
    have hcmp : ((2 * (2 * n : ℕ) * a) * gaussianWeight g o a o) * (1 - s) ≤
        (2 * (2 * n : ℕ) * a) * gaussianWeight g o a o :=
      mul_le_of_le_one_right hfac hdle
    have hdiv : (2 * (2 * n : ℕ) * a) * gaussianWeight g o a o ≤
        ((2 * (2 * n : ℕ) * a) * gaussianWeight g o a o) / (1 - s) :=
      (le_div_iff₀ hd).mpr hcmp
    calc
      _ = -(((2 * (2 * n : ℕ) * a) * gaussianWeight g o a o) /
          (1 - s)) := by ring
      _ ≤ -((2 * (2 * n : ℕ) * a) * gaussianWeight g o a o) :=
        neg_le_neg hdiv
      _ ≤ _ := by convert htrace using 1 <;> ring
  · obtain ⟨S, basis, hS, hcontact, hlower, htrace⟩ :=
      exists_gaussianLowerSupport_interior g hK hR o q (Ne.symm hqo) hs ha
    refine ⟨S, basis, hS, hcontact, hlower, ?_⟩
    convert htrace using 1 <;> ring

/-- The precise original Gaussian weak Laplacian coefficient follows from
local supports at every interior fraction and the one general transfer
principle.  All integrability is proved independently of the transfer. -/
theorem gaussianWeight_weak_laplacian_of_transfer_sharp
    (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ z, (ricci g.form z).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (htransfer : PhysicalLowerSupportToWeakGap g μ)
    (o : M.Carrier) {a : ℝ} (ha : 0 ≤ a)
    {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ)
    (hcψ : HasCompactSupport ψ) (hψnonneg : ∀ y, 0 ≤ ψ y) :
    (-(2 * n : ℕ) * a) *
      (∫ y, gaussianWeight g o a y * ψ y ∂μ) ≤
      ∫ y, gaussianWeight g o a y * laplacian g.form ψ y ∂μ := by
  let I : ℝ := ∫ y, gaussianWeight g o a y * ψ y ∂μ
  let J : ℝ := ∫ y, gaussianWeight g o a y * laplacian g.form ψ y ∂μ
  change (-(2 * n : ℕ) * a) * I ≤ J
  have hc : ContinuousAt (fun s : ℝ =>
      (-((2 * n : ℕ) * a / (1 - s))) * I) 0 := by
    have hden : ContinuousAt (fun s : ℝ => 1 - s) 0 :=
      continuousAt_const.sub continuousAt_id
    have hq : ContinuousAt (fun s : ℝ => (2 * n : ℕ) * a / (1 - s)) 0 :=
      continuousAt_const.div hden (by norm_num)
    exact hq.neg.mul continuousAt_const
  have hlim : Tendsto (fun s : ℝ =>
      (-((2 * n : ℕ) * a / (1 - s))) * I) (𝓝[>] 0)
      (𝓝 ((-(2 * n : ℕ) * a) * I)) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with s hs0 hs1
  exact htransfer hK hμ _ _ (gaussianWeight_continuous g o a)
    (gaussianWeight_hasPhysicalLowerSupports_fraction g hK hR o ha ⟨hs0, hs1⟩)
    ψ hψ hcψ hψnonneg
    (gaussianWeight_integrable_laplacian_test g μ hμ o a hψ hcψ)
    (gaussianWeight_integrable_compact_test g μ hμ o a hψ hcψ)

/-- The user-facing compact-test package: both real integrals are genuine,
and the complex Laplacian has the exact dimensional lower coefficient.  Its
sole unproved premise is the explicitly named general C²-support transfer. -/
theorem gaussianWeight_compact_test_package_of_transfer
    (g : SmoothMetric M) (hK : IsKahler g)
    (hR : ∀ z, (ricci g.form z).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (htransfer : PhysicalLowerSupportToWeakGap g μ)
    (o : M.Carrier) {a : ℝ} (ha : 0 < a)
    {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ)
    (hcψ : HasCompactSupport ψ) (hψnonneg : ∀ y, 0 ≤ ψ y) :
    Integrable (fun y => gaussianWeight g o a y * ψ y) μ ∧
    Integrable (fun y => gaussianWeight g o a y * laplacian g.form ψ y) μ ∧
    (∫ y, gaussianWeight g o a y * laplacian g.form ψ y ∂μ) ≥
      -(2 * (n : ℝ) * a) *
        (∫ y, gaussianWeight g o a y * ψ y ∂μ) := by
  refine ⟨gaussianWeight_integrable_compact_test g μ hμ o a hψ hcψ,
    gaussianWeight_integrable_laplacian_test g μ hμ o a hψ hcψ, ?_⟩
  convert gaussianWeight_weak_laplacian_of_transfer_sharp g hK hR μ hμ
    htransfer o ha.le hψ hcψ hψnonneg using 1 <;> norm_num [Nat.cast_mul] <;> ring

end Yau.LeafProofs.L19Aux
