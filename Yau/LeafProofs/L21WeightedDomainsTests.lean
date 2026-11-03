import Yau.LeafProofs.L21WeightedDomainsMeasure
import Yau.LeafProofs.L21WeakLocality

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

/-- Multiplication by the actual reciprocal density stays a genuine
compact test: its support remains strictly inside the smooth weight domain. -/
def weightedDensityInverseTest (K : ℝ) (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    CompactTest (Metric.ball (0 : X n) 1) := by
  let f : X n → ℂ := fun x => (Real.exp (boundaryWeight K x) : ℂ)*ψ x
  have hs : tsupport f ⊆ tsupport ψ := tsupport_mul_subset_right
  have hf : ContDiffOn ℝ ∞ f (Metric.ball 0 1) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (Real.contDiff_exp.comp_contDiffOn (contDiffOn_boundaryWeight K))).mul ψ.property.1.contDiffOn
  exact ⟨f,contDiff_of_contDiffOn_tsupport_subset Metric.isOpen_ball hf hs ψ.property.2.2,
    ψ.property.2.1.of_isClosed_subset (isClosed_tsupport _) hs,hs.trans ψ.property.2.2⟩

theorem inner_compactToWeightedScalar (K : ℝ) (hK : 0 ≤ K)
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) (u : WeightedScalar n K) :
    inner ℂ (compactToWeightedScalar K hK ψ) u =
      ∫ x, star (ψ x)*u x*(Real.exp (-boundaryWeight K x) : ℂ) ∂Yau.lebesgueC n := by
  rw [L2.inner_def]
  have hEq : (∫ x, inner ℂ ((compactToWeightedScalar K hK ψ : X n → ℂ) x) (u x)
      ∂weightedBallMeasure n K) =
      ∫ x, star (ψ x)*u x ∂weightedBallMeasure n K := by
    apply integral_congr_ae
    filter_upwards [compactToWeightedScalar_coeFn K hK ψ] with x hx
    rw [hx]
    exact RCLike.inner_apply' _ _
  rw [hEq,integral_weightedBallMeasure]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (ψ.property.2.2 hh))
    simp only [hz,star_zero,zero_mul,smul_zero])]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Complex.real_smul,smul_eq_mul]
  ring

theorem inner_weightedDensityInverseTest (K : ℝ) (hK : 0 ≤ K)
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) (u : WeightedScalar n K) :
    inner ℂ (compactToWeightedScalar K hK (weightedDensityInverseTest K ψ)) u =
      ∫ x, star (ψ x)*u x ∂Yau.lebesgueC n := by
  rw [inner_compactToWeightedScalar]
  apply integral_congr_ae
  filter_upwards [] with x
  change star ((Real.exp (boundaryWeight K x) : ℂ)*ψ x)*u x*
    (Real.exp (-boundaryWeight K x) : ℂ) = _
  rw [star_mul,show star (Real.exp (boundaryWeight K x) : ℂ) =
    (Real.exp (boundaryWeight K x) : ℂ) from Complex.conj_ofReal _]
  have he : (Real.exp (boundaryWeight K x) : ℂ)*(Real.exp (-boundaryWeight K x) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    simp
  calc
    _ = ((Real.exp (boundaryWeight K x) : ℂ)*(Real.exp (-boundaryWeight K x) : ℂ))*
      (star (ψ x)*u x) := by ring
    _ = _ := by rw [he,one_mul]

/-- Genuine compact tests separate the weighted Hilbert space. The proof
uses the original Lebesgue distribution tests and local L² representatives. -/
theorem weightedScalar_eq_zero_of_compact_pairings (K : ℝ) (hK : 0 ≤ K)
    (u : WeightedScalar n K)
    (hPair : ∀ ψ : CompactTest (Metric.ball (0 : X n) 1),
      inner ℂ (compactToWeightedScalar K hK ψ) u = 0) : u = 0 := by
  have hZero : LocallyL2On (fun _ : X n => (0 : ℂ)) (Metric.ball 0 1) := by
    intro S hS hSB
    exact MemLp.zero
  have hRaw : (u : X n → ℂ) =ᵐ[(Yau.lebesgueC n).restrict (Metric.ball 0 1)] (fun _ => 0) := by
    apply complex_ae_eq_of_test_integrals_eq Metric.isOpen_ball (weightedScalar_locallyL2On K u) hZero
    intro ψ hψ hcψ hsψ
    let ψC : CompactTest (Metric.ball (0 : X n) 1) :=
      ⟨fun x => (ψ x : ℂ),Complex.ofRealCLM.contDiff.comp hψ,
        hcψ.comp_left Complex.ofReal_zero,(tsupport_comp_subset Complex.ofReal_zero ψ).trans hsψ⟩
    have ht := hPair (weightedDensityInverseTest K ψC)
    rw [inner_weightedDensityInverseTest] at ht
    calc
      _ = ∫ x, star (ψC x)*u x ∂Yau.lebesgueC n := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [ψC,Complex.star_def,Complex.conj_ofReal,mul_comm]
      _ = 0 := ht
      _ = _ := by simp
  apply Lp.ext
  have hw := (weightedBall_ae_eq_iff K (u : X n → ℂ) (fun _ => 0)).mpr hRaw
  filter_upwards [hw,Lp.coeFn_zero (E := ℂ) (p := 2) (μ := weightedBallMeasure n K)] with x hx hzero
  exact hx.trans hzero.symm


/-- The actual scalar compact core is total in the weighted Hilbert space. -/
theorem weightedCompactScalar_span_dense (K : ℝ) (hK : 0 ≤ K) :
    Dense (Submodule.span ℂ (Set.range (compactToWeightedScalar (n := n) K hK)) :
      Set (WeightedScalar n K)) := by
  let P := Submodule.span ℂ (Set.range (compactToWeightedScalar (n := n) K hK))
  have hOrth : Pᗮ = ⊥ := by
    apply bot_unique
    intro u hu
    change u = 0
    apply weightedScalar_eq_zero_of_compact_pairings K hK u
    intro ψ
    exact (P.mem_orthogonal u).mp hu _ (Submodule.subset_span ⟨ψ,rfl⟩)
  have hTop : P.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.mpr hOrth
  rw [dense_iff_closure_eq,← Submodule.topologicalClosure_coe]
  change (P.topologicalClosure : Set (WeightedScalar n K)) = univ
  rw [hTop]
  rfl

def weightedConjugateTest {O : Set (X n)} (ψ : CompactTest O) : CompactTest O :=
  ⟨fun x => star (ψ x),(starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp ψ.property.1,
    ψ.property.2.1.comp_left (map_zero (starL' ℝ : ℂ ≃L[ℝ] ℂ)),
    (tsupport_comp_subset (map_zero (starL' ℝ : ℂ ≃L[ℝ] ℂ)) ψ).trans ψ.property.2.2⟩

/-- The unweighted distribution pairing is an actual bounded functional
on weighted L², because its test is compactly supported inside the ball. -/
def weightedCompactFunctional (K : ℝ) (hK : 0 ≤ K)
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) : WeightedScalar n K →L[ℂ] ℂ :=
  innerSL ℂ (compactToWeightedScalar K hK (weightedDensityInverseTest K (weightedConjugateTest ψ)))

theorem weightedCompactFunctional_apply (K : ℝ) (hK : 0 ≤ K)
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) (u : WeightedScalar n K) :
    weightedCompactFunctional K hK ψ u = ∫ x, ψ x*u x ∂Yau.lebesgueC n := by
  change inner ℂ (compactToWeightedScalar K hK
    (weightedDensityInverseTest K (weightedConjugateTest ψ))) u = _
  rw [inner_weightedDensityInverseTest]
  apply integral_congr_ae
  filter_upwards [] with x
  change star (star (ψ x))*u x = _
  rw [star_star]

/-- The functional reads every representative of the same weighted L²
class as the same genuine unweighted distribution. -/
theorem weightedCompactFunctional_apply_representative (K : ℝ) (hK : 0 ≤ K)
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) (u : WeightedScalar n K)
    {u' : X n → ℂ} (hRep : u' =ᵐ[weightedBallMeasure n K] (u : X n → ℂ)) :
    weightedCompactFunctional K hK ψ u = ∫ x, ψ x*u' x ∂Yau.lebesgueC n := by
  rw [weightedCompactFunctional_apply]
  have hLoc := (weightedBall_ae_eq_iff K u' (u : X n → ℂ)).mp hRep
  have hFull := (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hLoc
  apply integral_congr_ae
  filter_upwards [hFull] with x hx
  by_cases hxB : x ∈ Metric.ball (0 : X n) 1
  · rw [hx hxB]
  · have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hxB (ψ.property.2.2 hh))
    rw [hz,zero_mul,zero_mul]


theorem weightedCompactFunctional_separates (K : ℝ) (hK : 0 ≤ K)
    (u : WeightedScalar n K)
    (hZero : ∀ ψ : CompactTest (Metric.ball (0 : X n) 1), weightedCompactFunctional K hK ψ u = 0) :
    u = 0 := by
  apply weightedScalar_eq_zero_of_compact_pairings K hK u
  intro ψ
  have hh := hZero (weightedDensityInverseTest (-K) (weightedConjugateTest ψ))
  rw [weightedCompactFunctional_apply] at hh
  rw [inner_compactToWeightedScalar]
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [] with x
  change star (ψ x)*u x*(Real.exp (-boundaryWeight K x) : ℂ) =
    ((Real.exp (boundaryWeight (-K) x) : ℂ)*star (ψ x))*u x
  simp only [boundaryWeight,neg_div]
  ring

end Yau.LeafProofs.L21Aux
