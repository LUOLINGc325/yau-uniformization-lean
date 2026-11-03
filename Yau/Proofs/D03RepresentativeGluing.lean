import Yau.Proofs.D03RepresentativeScalar

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace Yau.Proofs.D03Aux
open Yau Yau.LeafProofs.L21Aux

/-- Continuous holomorphic local representatives that equal the same rough
function a.e. glue pointwise. Countability enters only in the global a.e. step. -/
theorem exists_holomorphic_of_locally_ae
    {O : Set (ComplexVector 1)}
    (u : ComplexVector 1 → ℂ)
    (hlocal : ∀ x ∈ O, ∃ U : Set (ComplexVector 1), IsOpen U ∧
      x ∈ U ∧ U ⊆ O ∧ ∃ b : ComplexVector 1 → ℂ,
        DifferentiableOn ℂ b U ∧ b =ᵐ[(Yau.lebesgueC 1).restrict U] u) :
    ∃ b : ComplexVector 1 → ℂ, DifferentiableOn ℂ b O ∧
      b =ᵐ[(Yau.lebesgueC 1).restrict O] u := by
  classical
  have : (Yau.lebesgueC 1).IsOpenPosMeasure := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  choose U hUopen hxU hUO b hb hbae using fun x : O => hlocal x x.property
  have hagree (i j : O) : EqOn (b i) (b j) (U i ∩ U j) := by
    have hiAE : b i =ᵐ[(Yau.lebesgueC 1).restrict (U i ∩ U j)] u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hbae i)
    have hjAE : b j =ᵐ[(Yau.lebesgueC 1).restrict (U i ∩ U j)] u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hbae j)
    have hijAE : b i =ᵐ[(Yau.lebesgueC 1).restrict (U i ∩ U j)] b j := hiAE.trans hjAE.symm
    exact Measure.eqOn_open_of_ae_eq hijAE ((hUopen i).inter (hUopen j))
      ((hb i).continuousOn.mono inter_subset_left)
      ((hb j).continuousOn.mono inter_subset_right)
  let B : ComplexVector 1 → ℂ := fun x => if hx : x ∈ O then b ⟨x, hx⟩ x else 0
  have hBU (i : O) : EqOn B (b i) (U i) := by
    intro x hx
    have hxO := hUO i hx
    dsimp only [B]
    rw [dif_pos hxO]
    exact hagree ⟨x, hxO⟩ i ⟨hxU ⟨x, hxO⟩, hx⟩
  refine ⟨B, ?_, ?_⟩
  · intro x hx
    let i : O := ⟨x, hx⟩
    have hBi : B =ᶠ[𝓝 x] b i :=
      eventually_of_mem ((hUopen i).mem_nhds (hxU i)) (hBU i)
    exact (((hb i) x (hxU i)).differentiableAt
      ((hUopen i).mem_nhds (hxU i))).congr_of_eventuallyEq hBi |>.differentiableWithinAt
  · have hcover : (⋃ i : O, U i) = O := by
      apply subset_antisymm
      · exact iUnion_subset hUO
      · intro x hx
        exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
    obtain ⟨T, hTcount, hTcover⟩ := TopologicalSpace.isOpen_iUnion_countable U hUopen
    have hTcoverO : (⋃ i ∈ T, U i) = O := hTcover.trans hcover
    rw [← hTcoverO]
    apply (ae_eq_restrict_biUnion_iff U hTcount B u).mpr
    intro i hi
    have hBi : B =ᵐ[(Yau.lebesgueC 1).restrict (U i)] b i := by
      filter_upwards [ae_restrict_mem (hUopen i).measurableSet] with x hx
      exact hBU i hx
    exact hBi.trans (hbae i)

/-- Scalar weak dbar regularity on an arbitrary open one-dimensional model
domain, including the actual a.e. equality to the input coefficient. -/
theorem exists_holomorphic_of_weak_dbar_zero
    {O : Set (ComplexVector 1)} (hO : IsOpen O)
    (u : ComplexVector 1 → ℂ) (hu : LocallyL2On u O)
    (hweak : ∀ (ψ : ComplexVector 1 → ℂ), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ O →
      (∫ x, u x * wirtBar ψ x (stdVec 0) ∂Yau.lebesgueC 1) = 0) :
    ∃ b : ComplexVector 1 → ℂ, DifferentiableOn ℂ b O ∧
      b =ᵐ[(Yau.lebesgueC 1).restrict O] u := by
  apply exists_holomorphic_of_locally_ae u
  intro x hx
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO x hx
  let R := Metric.ball x (r / 2)
  have hR : IsOpen R := Metric.isOpen_ball
  have hcl : closure R = Metric.closedBall x (r / 2) := closure_ball x ((half_pos hr).ne')
  have hcR : IsCompact (closure R) := by
    rw [hcl]
    exact isCompact_closedBall x (r / 2)
  have hRO : closure R ⊆ O := by
    rw [hcl]
    exact (Metric.closedBall_subset_ball (half_lt_self hr)).trans hrO
  obtain ⟨b, _, hb, hbae⟩ := exists_inner_holomorphic_of_weak_dbar_zero hO u hu hweak hR hcR hRO
  exact ⟨R, hR, Metric.mem_ball_self (half_pos hr),
    subset_closure.trans hRO, b, hb, hbae⟩

section OriginalBundle
open Yau.BundleDbar

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The exact weak top form has holomorphic vector coefficients in every
original local chart/frame, retaining the same coefficients a.e. -/
theorem exists_holomorphic_top_coefficients
    (W : NQForm E 0) (hW : WeakDbar (r := r) E W 0) (a : M.Carrier) :
    ∃ F : ComplexVector 1 → ComplexVector r,
      DifferentiableOn ℂ F (localDomain (r := r) E a) ∧
      F =ᵐ[(Yau.lebesgueC 1).restrict (localDomain (r := r) E a)]
        (fun z => coefficients (r := r) E W a z Fin.elim0) := by
  classical
  have hscalar (α : Fin r) : ∃ b : ComplexVector 1 → ℂ,
      DifferentiableOn ℂ b (localDomain (r := r) E a) ∧
      b =ᵐ[(Yau.lebesgueC 1).restrict (localDomain (r := r) E a)]
        (fun z => coefficients (r := r) E W a z Fin.elim0 α) := by
    apply exists_holomorphic_of_weak_dbar_zero
      (Yau.LeafProofs.L14Aux.localDomain_isOpen (r := r) E a)
      (fun z => coefficients (r := r) E W a z Fin.elim0 α)
    · intro K hK hKO
      exact Yau.LeafProofs.L14Aux.locallyL2_coefficients_memLp
        (r := r) E W hW.1 a Fin.elim0 α K hK hKO
    · intro ψ hψ hcψ hsψ
      have ht := ((Yau.LeafProofs.L14Aux.weakDbar_zero_iff_component_tests
        (r := r) E W (0 : NQForm E 1)).mp hW).2.2 a 0 α ψ hψ hcψ hsψ
      simpa only [Yau.LeafProofs.L14Aux.coefficients_zero (r := r) E,
        zero_mul, integral_zero, neg_eq_zero] using ht.symm
  choose b hb hbae using hscalar
  let F : ComplexVector 1 → ComplexVector r := fun z => WithLp.toLp 2 (fun α => b α z)
  refine ⟨F, (differentiableOn_piLp 2).mpr hb, ?_⟩
  filter_upwards [ae_all_iff.mpr hbae] with z hz
  ext α
  exact hz α

end OriginalBundle

end Yau.Proofs.D03Aux
