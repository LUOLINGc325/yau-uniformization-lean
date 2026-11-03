import Yau.Proofs.C04TangentComparison
import Yau.LeafProofs.L23FieldMetric

/-! Metric comparison along actual smooth paths, without exchanging the
different tangent norm instances belonging to the two fields. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter
namespace Yau.Proofs.C04RescaledTubeAux
open Yau Blueprint LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

def fieldPathSpeed (k : HermitianField M) (f : ℝ → M.Carrier) (t : ℝ) : ℝ :=
  Real.sqrt (2 * hermitianNormSq (k (f t))
    (L12Aux.realTangentEquiv (f t) (L12Aux.realCurveVelocity f t)))

def fieldPathLength (k : HermitianField M) (f : ℝ → M.Carrier) (a b : ℝ) : ENNReal :=
  ∫⁻ t in Set.Icc a b, ENNReal.ofReal (fieldPathSpeed k f t)

theorem fieldPathLength_eq_pathELength (k : HermitianField M)
    (f : ℝ → M.Carrier) (a b : ℝ) :
    letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
      fun x => L12Aux.underlyingRealTangentNormedAddCommGroup k x
    fieldPathLength k f a b = Manifold.pathELength 𝓘(ℝ, ComplexVector n) f a b := by
  letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => L12Aux.underlyingRealTangentNormedAddCommGroup k x
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  change ENNReal.ofReal (fieldPathSpeed k f t) = ‖L12Aux.realCurveVelocity f t‖ₑ
  rw [← ofReal_norm, L12Aux.underlyingRealTangent_norm]
  rfl

theorem fieldPathSpeed_le (k g : HermitianField M) (f : ℝ → M.Carrier)
    (t c : ℝ) (hc : 0 ≤ c)
    (hkg : HermLE (gMat k (f t)) ((c : ℂ) • gMat g (f t))) :
    fieldPathSpeed k f t ≤ Real.sqrt c * fieldPathSpeed g f t := by
  have hh := C04Aux.tangent_norm_le_of_HermLE k g (f t) c hkg
    (L12Aux.realTangentEquiv (f t) (L12Aux.realCurveVelocity f t))
  unfold fieldPathSpeed
  have hs := Real.sqrt_le_sqrt (show 2 * hermitianNormSq (k (f t))
      (L12Aux.realTangentEquiv (f t) (L12Aux.realCurveVelocity f t)) ≤
    c * (2 * hermitianNormSq (g (f t))
      (L12Aux.realTangentEquiv (f t) (L12Aux.realCurveVelocity f t))) by nlinarith)
  rwa [Real.sqrt_mul hc] at hs

theorem fieldPathLength_le (k g : HermitianField M) (f : ℝ → M.Carrier)
    (a b c : ℝ) (hc : 0 ≤ c)
    (hkg : ∀ t ∈ Set.Icc a b, HermLE (gMat k (f t)) ((c : ℂ) • gMat g (f t))) :
    fieldPathLength k f a b ≤ ENNReal.ofReal (Real.sqrt c) * fieldPathLength g f a b := by
  unfold fieldPathLength
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  exact ENNReal.ofReal_le_ofReal (fieldPathSpeed_le k g f t c hc (hkg t ht))

theorem fieldPathLength_mono (k : HermitianField M) (f : ℝ → M.Carrier)
    {a b A B : ℝ} (hA : A ≤ a) (hB : b ≤ B) :
    fieldPathLength k f a b ≤ fieldPathLength k f A B :=
  lintegral_mono_set (Set.Icc_subset_Icc hA hB)

theorem distance_le_fieldPathLength (k : HermitianField M) (hk : MetricSmooth k)
    (f : ℝ → M.Carrier) {a b : ℝ} (hab : a ≤ b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f (Set.Icc a b)) :
    ENNReal.ofReal (inducedDistance k (f a) (f b)) ≤ fieldPathLength k f a b := by
  letI := L12Aux.manifold_realSmooth M
  letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => L12Aux.underlyingRealTangentNormedAddCommGroup k x
  letI : ∀ x : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => L12Aux.underlyingRealTangentInnerProductSpace k x
  rw [fieldPathLength_eq_pathELength, L23Aux.inducedDistance_eq_riemannianEDist k hk]
  exact Manifold.riemannianEDist_le_pathELength hf rfl rfl hab

theorem exists_short_smooth_path (k : HermitianField M) (hk : MetricSmooth k)
    (x y : M.Carrier) {r : ℝ} (hr : inducedDistance k x y < r) :
    ∃ f : ℝ → M.Carrier, f 0 = x ∧ f 1 = y ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f ∧
      fieldPathLength k f 0 1 < ENNReal.ofReal r := by
  letI := L12Aux.manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => L12Aux.underlyingRealTangentNormedAddCommGroup k z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => L12Aux.underlyingRealTangentInnerProductSpace k z
  letI := L23Aux.realEMetricSpace k hk
  have hrpos : 0 < r := (L23Aux.inducedDistance_nonneg k hk x y).trans_lt hr
  have hh : Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y < ENNReal.ofReal r := by
    rw [← L23Aux.inducedDistance_eq_riemannianEDist k hk]
    exact (ENNReal.ofReal_lt_ofReal_iff hrpos).2 hr
  obtain ⟨f, hx, hy, hf, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hh zero_lt_one
  refine ⟨f, hx, hy, hf, ?_⟩
  rwa [fieldPathLength_eq_pathELength]

theorem distance_le_of_HermLE (k g : HermitianField M)
    (hk : MetricSmooth k) (hg : MetricSmooth g) {c : ℝ} (hc : 0 < c)
    (hkg : ∀ x, HermLE (gMat k x) ((c : ℂ) • gMat g x)) (x y : M.Carrier) :
    inducedDistance k x y ≤ Real.sqrt c * inducedDistance g x y := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  have hbpos : 0 < b := (mul_nonneg hs.le
    (L23Aux.inducedDistance_nonneg g hg x y)).trans_lt hb
  have hshort : inducedDistance g x y < b / Real.sqrt c := by
    apply (lt_div_iff₀ hs).2
    simpa only [mul_comm] using hb
  obtain ⟨f, hzero, hone, hf, hlen⟩ := exists_short_smooth_path g hg x y hshort
  have hd := distance_le_fieldPathLength k hk f zero_le_one hf.contMDiffOn
  have hcomp := fieldPathLength_le k g f 0 1 c hc.le (fun t _ => hkg (f t))
  have hmul := ENNReal.mul_lt_mul_right
    (ENNReal.ofReal_pos.2 hs).ne' ENNReal.ofReal_ne_top hlen
  have heq : ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal (b / Real.sqrt c) =
      ENNReal.ofReal b := by
    rw [← ENNReal.ofReal_mul hs.le, mul_div_cancel₀ b hs.ne']
  rw [heq] at hmul
  rw [hzero, hone] at hd
  exact ((ENNReal.ofReal_lt_ofReal_iff hbpos).1 (hd.trans hcomp |>.trans_lt hmul)).le

end Yau.Proofs.C04RescaledTubeAux
