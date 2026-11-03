import Yau.Proofs.D03ApproximationHolomorphic

set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Filter Set Bundle
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.Proofs.D03Aux
open Yau Yau.BundleDbar Yau.Blueprint.BundlePresentation
open Yau.LeafProofs.L14Aux

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Compute the smooth dbar of the actual cutoff top form in the original
chart/frame. This is the exact B01 source tensor used by the L14 solve. -/
theorem cutoff_topForm_isDbarOf
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (s : Section E)
    (hs : HolomorphicSection (r := r) E s) (n : ℕ) :
    IsDbarOf (r := r) E (B01Aux.sectionTopForm E c (cutoffSection E c s n))
      (B01Aux.cutoffSourceForm E c s (cutoff c n)) := by
  intro a z hz I α
  have hI : I = fun _ : Fin 1 => (0 : Fin 1) := Subsingleton.elim _ _
  subst I
  let J : ComplexVector 1 → ℂ := fun w => wirt (fun t => c (chartInv a t)) w (stdVec 0)
  let χ : ComplexVector 1 → ℂ := fun w => (cutoff c n (chartInv a w) : ℂ)
  let S : ComplexVector 1 → ℂ := fun w => sectionCoefficients (r := r) E s a w α
  have hJD : DifferentiableAt ℂ J z :=
    ((disc_chart_wirt_differentiableOn c hc a) z hz.1).differentiableAt
      ((isOpen_extChartAt_target (I := ComplexModel 1) a).mem_nhds hz.1)
  have hSD : DifferentiableAt ℂ S z :=
    (((differentiableOn_piLp 2).mp (hs a) α) z hz).differentiableAt
      ((localDomain_isOpen (r := r) E a).mem_nhds hz)
  have hχC : ContDiffOn ℝ ∞ χ (chartTarget a) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (cutoff_smooth c hc n a)
  have hχD : DifferentiableAt ℝ χ z :=
    ((hχC.differentiableOn (by simp)) z hz.1).differentiableAt
      ((isOpen_extChartAt_target (I := ComplexModel 1) a).mem_nhds hz.1)
  have heq : (fun w => coefficients (r := r) E
      (B01Aux.sectionTopForm E c (cutoffSection E c s n)) a w Fin.elim0 α) =ᶠ[𝓝 z]
      (fun w => J w * χ w * S w) := by
    filter_upwards [(localDomain_isOpen (r := r) E a).mem_nhds hz] with w hw
    rw [sectionTopForm_coefficients E c hc _ a w hw]
    rw [sectionCoefficients_cutoffSection E c s n a w]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hW : wirtBar (fun w => coefficients (r := r) E
      (B01Aux.sectionTopForm E c (cutoffSection E c s n)) a w Fin.elim0 α) z (stdVec 0) =
      wirtBar (fun w => J w * χ w * S w) z (stdVec 0) := by
    unfold wirtBar
    rw [heq.fderiv_eq]
  have hχbar : wirtBar χ z (stdVec 0) =
      discDbarScalar c (cutoff c n) (chartInv a z) * star (J z) :=
    chart_dbar_cutoff (r := r) E c hc n a z hz.1
  have hproduct : wirtBar (fun w => J w * χ w * S w) z (stdVec 0) =
      (discDbarScalar c (cutoff c n) (chartInv a z) * star (J z) * J z) * S z := by
    rw [wirtBar_mul_rule (fun w => J w * χ w) S z (stdVec 0)
      ((hJD.restrictScalars ℝ).mul hχD) (hSD.restrictScalars ℝ),
      wirtBar_mul_rule J χ z (stdVec 0) (hJD.restrictScalars ℝ) hχD,
      wirtBar_eq_zero_of_complex_differentiable J z (stdVec 0) hJD,
      wirtBar_eq_zero_of_complex_differentiable S z (stdVec 0) hSD,
      zero_mul, mul_zero, add_zero, zero_add, hχbar]
    ring
  have hindex : (fun _ : Fin 0 => (0 : Fin 1)) = Fin.elim0 := Subsingleton.elim _ _
  have hsource := congrArg (fun v : ComplexVector r => v α)
    (B01Aux.cutoffSourceForm_coefficients E c hc s (cutoff c n) a z hz (fun _ => 0))
  change coefficients (r := r) E (B01Aux.cutoffSourceForm E c s (cutoff c n)) a z (fun _ => 0) α = _
  rw [hsource]
  change (discDbarScalar c (cutoff c n) (chartInv a z) * star (J z) * J z) * S z = _
  rw [← hproduct, ← hW]
  unfold dbarCoefficients
  change _ = ∑ k : Fin 1, (-1 : ℂ) ^ k.val * wirtBar
    (fun w => coefficients (r := r) E (B01Aux.sectionTopForm E c (cutoffSection E c s n))
      a w (fun _ : Fin 0 => (0 : Fin 1)) α) z (stdVec 0)
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_mul, hindex]

/-- The exact smooth cutoff tensor is a genuine weak solution of the same
source; no new scalar solver or regularized unknown is substituted. -/
theorem cutoff_topForm_weakDbar
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (s : Section E)
    (hs : HolomorphicSection (r := r) E s) (n : ℕ) :
    WeakDbar (r := r) E (B01Aux.sectionTopForm E c (cutoffSection E c s n))
      (B01Aux.cutoffSourceForm E c s (cutoff c n)) :=
  weakDbar_of_smooth_isDbarOf (r := r) E _ _
    (cutoff_topForm_smooth E c hc s hs n)
    (B01Aux.cutoffSourceForm_smooth E c hc s hs (cutoff c n) (cutoff_smooth c hc n))
    (cutoff_topForm_isDbarOf E c hc s hs n)

/-- The actual weak correction has a holomorphic original-bundle difference.
The equality is a.e. for the exact original ordinary-area measure. -/
theorem exists_holomorphic_cutoff_difference
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (hE : Holomorphic (r := r) E) (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (s : Section E) (hs : HolomorphicSection (r := r) E s) (n : ℕ)
    (u : NQForm E 0) (v : Section E)
    (hu : WeakDbar (r := r) E u (B01Aux.cutoffSourceForm E c s (cutoff c n)))
    (hv : IsSectionTopForm E c v u) :
    ∃ b : Section E, HolomorphicSection (r := r) E b ∧
      (∀ᵐ x ∂Yau.Blueprint.BundlePresentation.discArea c,
        b x = (cutoff c n x : ℂ) • s x - v x) := by
  let T := B01Aux.sectionTopForm E c (cutoffSection E c s n)
  have hdiff := weakDbar_difference_zero E T u _ (cutoff_topForm_weakDbar E c hc s hs n) hu
  obtain ⟨b, hb, hAE⟩ := exists_holomorphic_section_of_weak_closed_top E c hc hE g μ hμ _ hdiff
  refine ⟨b, hb, ?_⟩
  filter_upwards [hAE] with x hx
  have heval := congrArg
    (fun W : {A : MixedTensor E x 0 // AntiComplexLinear E A} =>
      (W.1 Fin.elim0) (fun _ : Fin 1 => B01Aux.discCoordinateVector c x)) hx
  change (B01Aux.sectionTopForm E c b x).1 Fin.elim0
      (fun _ : Fin 1 => B01Aux.discCoordinateVector c x) = _ at heval
  rw [B01Aux.sectionTopForm_spec E c b, B01Aux.discCoordinateVector_map c hc, one_smul] at heval
  rw [nqForm_add_apply, nqForm_smul_apply] at heval
  simp only [AlternatingMap.add_apply, AlternatingMap.smul_apply] at heval
  have hTvalue : (T x).1 Fin.elim0 (fun _ : Fin 1 => B01Aux.discCoordinateVector c x) =
      (cutoff c n x : ℂ) • s x := by
    change (B01Aux.sectionTopForm E c (cutoffSection E c s n) x).1 Fin.elim0 _ = _
    rw [B01Aux.sectionTopForm_spec E c (cutoffSection E c s n),
      B01Aux.discCoordinateVector_map c hc, one_smul]
    rfl
  have huvalue : (u x).1 Fin.elim0 (fun _ : Fin 1 => B01Aux.discCoordinateVector c x) = v x := by
    rw [hv, B01Aux.discCoordinateVector_map c hc, one_smul]
  rw [hTvalue, huvalue, neg_one_smul] at heval
  exact heval.trans (sub_eq_add_neg _ _).symm


end Yau.Proofs.D03Aux
