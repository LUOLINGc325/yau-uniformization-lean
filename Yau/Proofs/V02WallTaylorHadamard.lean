import Yau.Proofs.V03CompactIntegralOperator
import Yau.Proofs.V03CompactParamSmoothness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The smooth divided difference is a genuine parameter integral of the
actual derivative. No division by the vanishing multiplier occurs. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof

abbrev UnitIntervalTrace := Set.Icc (0 : ℝ) 1

def unitIntervalTraceMeasure : Measure UnitIntervalTrace :=
  (volume.restrict (Set.Ioc (0 : ℝ) 1)).comap Subtype.val

instance : IsFiniteMeasure unitIntervalTraceMeasure := by
  letI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  exact inferInstanceAs (IsFiniteMeasure ((volume.restrict (Set.Ioc (0 : ℝ) 1)).comap
    (Subtype.val : UnitIntervalTrace → ℝ)))

theorem unitIntervalTraceIntegral_eq {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} {f : P × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ UnitIntervalTrace))
    {p : P} (hp : p ∈ U) :
    compactIntegralL unitIntervalTraceMeasure (compactParamTrace hf.continuousOn p) =
      ∫ s in (0 : ℝ)..1, f (p, s) := by
  change (∫ s : UnitIntervalTrace, compactParamTrace hf.continuousOn p s
    ∂unitIntervalTraceMeasure) = _
  calc
    _ = ∫ s : UnitIntervalTrace, f (p, s) ∂unitIntervalTraceMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun s => compactParamTrace_apply hf.continuousOn hp s)
    _ = _ := by
      rw [unitIntervalTraceMeasure, integral_subtype_comap
        (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (s := UnitIntervalTrace)
        measurableSet_Icc (fun s : ℝ => f (p, s)),
        Measure.restrict_restrict measurableSet_Icc,
        Set.inter_eq_right.mpr Set.Ioc_subset_Icc_self,
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

theorem unitIntervalIntegral_contDiffOn {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} (hU : IsOpen U) {f : P × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ UnitIntervalTrace)) :
    ContDiffOn ℝ ∞ (fun p => ∫ s in (0 : ℝ)..1, f (p, s)) U := by
  have hT := compactParamTrace_contDiffOn hU (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) hf
  have hh := (compactIntegralL unitIntervalTraceMeasure).contDiff.comp_contDiffOn hT
  exact hh.congr (fun p hp => (unitIntervalTraceIntegral_eq hf hp).symm)

variable {P T : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- The actual derivative, integrated along the scaled real segment. -/
def scaledHadamardFactor (F : P × T → ℝ) (m : P → ℝ) (A : P → T) (p : P) : ℝ :=
  ∫ s in (0 : ℝ)..1, fderiv ℝ F (p, s • (m p • A p)) (0, A p)

theorem scaledHadamardIntegrand_contDiffOn {Ω : Set (P × T)} (hΩ : IsOpen Ω)
    {F : P × T → ℝ} (hF : ContDiffOn ℝ ∞ F Ω)
    {U : Set P} {m : P → ℝ} (hm : ContDiffOn ℝ ∞ m U)
    {A : P → T} (hA : ContDiffOn ℝ ∞ A U)
    (hseg : ∀ p ∈ U, ∀ s ∈ Set.Icc (0 : ℝ) 1, (p, s • (m p • A p)) ∈ Ω) :
    ContDiffOn ℝ ∞ (fun w : P × ℝ =>
      fderiv ℝ F (w.1, w.2 • (m w.1 • A w.1)) (0, A w.1)) (U ×ˢ UnitIntervalTrace) := by
  have hm' : ContDiffOn ℝ ∞ (fun w : P × ℝ => m w.1) (U ×ˢ UnitIntervalTrace) :=
    hm.comp contDiffOn_fst (fun w hw => hw.1)
  have hA' : ContDiffOn ℝ ∞ (fun w : P × ℝ => A w.1) (U ×ˢ UnitIntervalTrace) :=
    hA.comp contDiffOn_fst (fun w hw => hw.1)
  have hh : ContDiffOn ℝ ∞ (fun w : P × ℝ => (w.1, w.2 • (m w.1 • A w.1)))
      (U ×ˢ UnitIntervalTrace) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.smul (hm'.smul hA'))
  exact ((hF.fderiv_of_isOpen hΩ (m := ∞) (by simp)).comp hh
    (fun w hw => hseg _ hw.1 _ hw.2)).clm_apply (contDiffOn_const.prodMk hA')

theorem scaledHadamardFactor_contDiffOn {Ω : Set (P × T)} (hΩ : IsOpen Ω)
    {F : P × T → ℝ} (hF : ContDiffOn ℝ ∞ F Ω)
    {U : Set P} (hU : IsOpen U) {m : P → ℝ} (hm : ContDiffOn ℝ ∞ m U)
    {A : P → T} (hA : ContDiffOn ℝ ∞ A U)
    (hseg : ∀ p ∈ U, ∀ s ∈ Set.Icc (0 : ℝ) 1, (p, s • (m p • A p)) ∈ Ω) :
    ContDiffOn ℝ ∞ (scaledHadamardFactor F m A) U :=
  unitIntervalIntegral_contDiffOn hU (scaledHadamardIntegrand_contDiffOn hΩ hF hm hA hseg)

theorem scaledHadamardFactor_zero {F : P × T → ℝ} {m : P → ℝ} {A : P → T}
    {p : P} (hA : A p = 0) : scaledHadamardFactor F m A p = 0 := by
  simp [scaledHadamardFactor, hA]
  exact map_zero _

theorem scaledHadamardFactor_identity {Ω : Set (P × T)} (hΩ : IsOpen Ω)
    {F : P × T → ℝ} (hF : ContDiffOn ℝ ∞ F Ω)
    {m : P → ℝ} {A : P → T} {p : P}
    (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, (p, s • (m p • A p)) ∈ Ω) :
    F (p, m p • A p) - F (p, 0) = m p * scaledHadamardFactor F m A p := by
  have hpath : Continuous (fun s : ℝ => (p, s • (m p • A p))) :=
    continuous_const.prodMk (continuous_id.smul continuous_const)
  have hder (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => F (p, t • (m p • A p)))
        (m p * fderiv ℝ F (p, s • (m p • A p)) (0, A p)) s := by
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by simpa using hs
    have hdiff := ((hF.contDiffAt (hΩ.mem_nhds (hseg s hs'))).differentiableAt (by simp)).hasFDerivAt
    have hh := hdiff.comp_hasDerivAt s
      ((hasDerivAt_const s p).prodMk ((hasDerivAt_id s).smul_const (m p • A p)))
    have hpair : ((0 : P), m p • A p) = m p • ((0 : P), A p) := by simp
    simpa only [Function.comp_def, id_eq, one_smul, hpair, map_smul, smul_eq_mul] using hh
  have hc : ContinuousOn (fun s : ℝ =>
      m p * fderiv ℝ F (p, s • (m p • A p)) (0, A p)) (Set.uIcc (0 : ℝ) 1) := by
    have hh := ((hF.fderiv_of_isOpen hΩ (m := ∞) (by simp)).continuousOn.comp hpath.continuousOn
      (fun (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) 1) => hseg s (by simpa using hs))).clm_apply (continuousOn_const (c := ((0 : P), A p)))
    exact continuousOn_const.mul hh
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hc.intervalIntegrable
  simpa only [one_smul, zero_smul, intervalIntegral.integral_const_mul, scaledHadamardFactor]
    using hFTC.symm

end Yau.Blueprint.V02WallTaylorProof
