import Yau.Proofs.V02FlowPicardSpace
import Yau.Proofs.V02FlowParameterIntegral
import Yau.Proofs.V03HolomorphicSmooth
import Mathlib.Topology.MetricSpace.Contracting

/-! The actual radial Bochner Picard operator on a closed product. -/

open scoped Topology ContDiff
open Filter MeasureTheory Metric

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open V03Proof

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V]

def picardRadialLinear (s : ℝ) : (ℂ × V) →L[ℂ] (ℂ × V) :=
  ((s : ℂ) • ContinuousLinearMap.id ℂ ℂ).prodMap (ContinuousLinearMap.id ℂ V)

@[simp] theorem picardRadialLinear_apply (s : ℝ) (p : ℂ × V) :
    picardRadialLinear s p = ((s : ℂ) * p.1, p.2) := rfl

theorem continuous_picardRadialLinear :
    Continuous (picardRadialLinear (V := V)) :=
  (Complex.continuous_ofReal.smul continuous_const).prod_mapL ℂ continuous_const

theorem norm_radial_time_le {s : ℝ} (hs : s ∈ Set.Icc 0 1) (t : ℂ) :
    ‖(s : ℂ) * t‖ ≤ ‖t‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact mul_le_of_le_one_left (norm_nonneg t) hs.2

theorem picardRadialLinear_mem_closed {a : V} {d R s : ℝ}
    (hs : s ∈ Set.Icc 0 1) {p : ℂ × V} (hp : p ∈ picardClosedDomain a d R) :
    picardRadialLinear s p ∈ picardClosedDomain a d R := by
  refine ⟨?_, hp.2⟩
  simpa only [picardRadialLinear_apply, mem_closedBall, dist_zero_right] using
    (norm_radial_time_le hs p.1).trans (by simpa using hp.1)

theorem picardRadialLinear_mem_open {a : V} {d R s : ℝ}
    (hs : s ∈ Set.Icc 0 1) {p : ℂ × V} (hp : p ∈ picardOpenDomain a d R) :
    picardRadialLinear s p ∈ picardOpenDomain a d R := by
  refine ⟨?_, hp.2⟩
  simpa only [picardRadialLinear_apply, mem_ball, dist_zero_right] using
    (norm_radial_time_le hs p.1).trans_lt (by simpa using hp.1)

theorem continuousOn_compactExtension {P F : Type*} [NormedAddCommGroup P]
    [NormedAddCommGroup F] {K : Set P} (u : C(K, F)) :
    ContinuousOn (compactExtension u) K := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert u.continuous using 1
  funext p
  exact compactExtension_of_mem u p.2

def picardIntegral {a : V} {d R : ℝ} (W : V → V)
    (u : C(picardClosedDomain a d R, V)) (p : ℂ × V) : V :=
  ∫ s in (0 : ℝ)..1, W (compactExtension u (picardRadialLinear s p))

def picardRaw {a : V} {d R : ℝ} (W : V → V)
    (u : C(picardClosedDomain a d R, V)) (p : ℂ × V) : V :=
  p.2 + p.1 • picardIntegral W u p

theorem picardRaw_continuousOn_closed {a : V} {d R M : ℝ} {Ω : Set V} {W : V → V}
    (hW : ContinuousOn W Ω) (hball : closedBall a (2 * d) ⊆ Ω)
    (hbound : ∀ z ∈ closedBall a (2 * d), ‖W z‖ ≤ M)
    {u : C(picardClosedDomain a d R, V)} (hu : u ∈ picardHolomorphicBall a d R) :
    ContinuousOn (picardRaw W u) (picardClosedDomain a d R) := by
  let K := picardClosedDomain a d R
  have hrad : Continuous (fun p : K × ℝ => picardRadialLinear p.2 p.1.1) :=
    ((continuous_picardRadialLinear (V := V)).comp continuous_snd).clm_apply
      (continuous_subtype_val.comp continuous_fst)
  have himage : ∀ p : K × ℝ, p ∈ Set.univ ×ˢ Set.uIcc (0 : ℝ) 1 →
      picardRadialLinear p.2 p.1.1 ∈ K := by
    intro p hp
    exact picardRadialLinear_mem_closed (by simpa using hp.2) p.1.2
  have huc := (continuousOn_compactExtension u).comp hrad.continuousOn himage
  have hcoord : ∀ p : K × ℝ, p ∈ Set.univ ×ˢ Set.uIcc (0 : ℝ) 1 →
      compactExtension u (picardRadialLinear p.2 p.1.1) ∈ closedBall a (2 * d) := by
    intro p hp
    rw [compactExtension_of_mem u (himage p hp)]
    exact picardHolomorphicBall_image a hu _
  have hcont := hW.comp huc (fun p hp => hball (hcoord p hp))
  have hI : Continuous (fun p : K => picardIntegral W u p.1) :=
    continuous_intervalIntegral_of_joint_bounded hcont
      (fun p s hs => hbound _ (hcoord (p, s) ⟨Set.mem_univ _, hs⟩))
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact (continuous_snd.comp continuous_subtype_val).add
    ((continuous_fst.comp continuous_subtype_val).smul hI)

theorem picardRaw_differentiableOn_open {a : V} {d R : ℝ} {Ω : Set V} {W : V → V}
    (hΩ : IsOpen Ω) (hW : DifferentiableOn ℂ W Ω)
    (hball : closedBall a (2 * d) ⊆ Ω)
    {u : C(picardClosedDomain a d R, V)} (hu : u ∈ picardHolomorphicBall a d R) :
    DifferentiableOn ℂ (picardRaw W u) (picardOpenDomain a d R) := by
  let O := picardOpenDomain a d R
  let A : (ℂ × V) → ℝ → V :=
    fun p s => W (compactExtension u (picardRadialLinear s p))
  let D : (ℂ × V) → ℝ → (ℂ × V) →L[ℂ] V := fun p s =>
    (fderiv ℂ W (compactExtension u (picardRadialLinear s p))).comp
      ((fderiv ℂ (compactExtension u) (picardRadialLinear s p)).comp (picardRadialLinear s))
  have hO : IsOpen O := picardOpenDomain_isOpen a d R
  have hrad : Continuous (fun p : (ℂ × V) × ℝ => picardRadialLinear p.2 p.1) :=
    ((continuous_picardRadialLinear (V := V)).comp continuous_snd).clm_apply continuous_fst
  have hradO : ∀ p ∈ O ×ˢ Set.Icc (0 : ℝ) 1, picardRadialLinear p.2 p.1 ∈ O :=
    fun p hp => picardRadialLinear_mem_open hp.2 hp.1
  have huc := hu.1.continuousOn.comp hrad.continuousOn hradO
  have huimage : ∀ p ∈ O ×ˢ Set.Icc (0 : ℝ) 1,
      compactExtension u (picardRadialLinear p.2 p.1) ∈ Ω := by
    intro p hp
    have hm := picardOpenDomain_subset_closedDomain a d R (hradO p hp)
    rw [compactExtension_of_mem u hm]
    exact hball (picardHolomorphicBall_image a hu _)
  have hAc : ContinuousOn (fun p : (ℂ × V) × ℝ => A p.1 p.2)
      (O ×ˢ Set.Icc 0 1) := hW.continuousOn.comp huc huimage
  have hDu := (complex_holomorphic_continuousOn_fderiv hO hu.1).comp
    hrad.continuousOn hradO
  have hDW := (complex_holomorphic_continuousOn_fderiv hΩ hW).comp huc huimage
  have hDc : ContinuousOn (fun p : (ℂ × V) × ℝ => D p.1 p.2)
      (O ×ˢ Set.Icc 0 1) :=
    hDW.clm_comp (hDu.clm_comp ((continuous_picardRadialLinear (V := V)).comp continuous_snd).continuousOn)
  have hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ O,
      HasFDerivAt (fun z => A z s) (D p s) p := by
    intro s hs p hp
    have hm := hradO (p, s) ⟨hp, hs⟩
    have hdu := ((hu.1 _ hm).differentiableAt (hO.mem_nhds hm)).hasFDerivAt
    have hdw := ((hW _ (huimage (p, s) ⟨hp, hs⟩)).differentiableAt
      (hΩ.mem_nhds (huimage (p, s) ⟨hp, hs⟩))).hasFDerivAt
    exact hdw.comp p (hdu.comp p (picardRadialLinear (V := V) s).hasFDerivAt)
  have hI : DifferentiableOn ℂ (picardIntegral W u) O :=
    differentiableOn_intervalIntegral_of_joint_fderiv hO zero_le_one hAc
      (fun s hs p hp => (hder s hs p hp).differentiableAt.differentiableWithinAt)
      (hDc.congr (fun p hp => (hder p.2 hp.2 p.1 hp.1).fderiv))
  exact differentiableOn_snd.add (differentiableOn_fst.smul hI)

end Yau.Blueprint.V02FlowProof
