import spec.CHAIN.HeatConcreteBindings

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.SmoothExhaustionAux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem realSmooth (M : ComplexManifold n) : IsManifold 𝓘(ℝ, ComplexVector n) ∞ M.Carrier := by
  apply isManifold_of_contDiffOn 𝓘(ℝ, ComplexVector n) ∞ M.Carrier
  intro e e' he he'
  have hc := (ComplexModel n).contDiffOn_extendCoordChange (n := ∞)
    (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas he')
  convert! hc.restrict_scalars ℝ using 1
  simp [ModelWithCorners.extendCoordChange_source,ComplexModel,mfld_simps]

theorem real_extChartAt_eq (x : M.Carrier) :
    extChartAt 𝓘(ℝ, ComplexVector n) x = extChartAt (ComplexModel n) x := rfl

theorem contDiffOn_inChart_of_contMDiff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : M.Carrier → F}
    (hf : ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, F) ∞ f) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => f (chartInv a z)) (chartTarget a) := by
  letI := realSmooth M
  have H := hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ComplexVector n)) a)
  change ContDiffOn ℝ ∞ (f ∘ (extChartAt (ComplexModel n) a).symm)
    (extChartAt (ComplexModel n) a).target
  simpa only [real_extChartAt_eq] using H.contDiffOn

theorem smoothFn_of_contMDiff {f : M.Carrier → ℝ}
    (hf : ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ f) : SmoothFn f :=
  contDiffOn_inChart_of_contMDiff hf

theorem continuous_of_smoothFn {f : M.Carrier → ℝ} (hf : SmoothFn f) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have HC := ((hf x).continuousOn.continuousAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds (mem_extChartAt_target x))).comp
      (continuousAt_extChartAt (I := ComplexModel n) x)
  apply HC.congr_of_eventuallyEq
  filter_upwards [extChartAt_source_mem_nhds (I := ComplexModel n) x] with y hy
  change f y=f (chartInv x (chartPt x y))
  exact (congrArg f ((extChartAt (ComplexModel n) x).left_inv hy)).symm

theorem isOpen_chartInv_image (a : M.Carrier) {V : Set (ComplexVector n)}
    (hV : IsOpen V) (hVa : V ⊆ chartTarget a) : IsOpen (chartInv a '' V) := by
  have heq : chartInv a '' V =
      (extChartAt (ComplexModel n) a).source ∩ (chartPt a) ⁻¹' V := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨(extChartAt (ComplexModel n) a).map_target (hVa hz),?_⟩
      change chartPt a (chartInv a z) ∈ V
      have hp : chartPt a (chartInv a z) = z := (extChartAt (ComplexModel n) a).right_inv (hVa hz)
      exact hp.symm ▸ hz
    · rintro ⟨hy,hz⟩
      exact ⟨chartPt a y,hz,(extChartAt (ComplexModel n) a).left_inv hy⟩
  rw [heq]
  exact (continuousOn_extChartAt (I := ComplexModel n) a).isOpen_inter_preimage
    (isOpen_extChartAt_source a) hV

def pushZero {F : Type*} [Zero F] (a : M.Carrier) (φ : ComplexVector n → F)
    (p : M.Carrier) : F :=
  @ite F (p ∈ (extChartAt (ComplexModel n) a).source) (Classical.propDecidable _)
    (φ (chartPt a p)) 0

theorem pushZero_chartInv {F : Type*} [Zero F] (a : M.Carrier) (φ : ComplexVector n → F)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) : pushZero a φ (chartInv a z) = φ z := by
  have hy : chartInv a z ∈ (extChartAt (ComplexModel n) a).source :=
    (extChartAt (ComplexModel n) a).map_target hz
  have hp : chartPt a (chartInv a z) = z := (extChartAt (ComplexModel n) a).right_inv hz
  simp only [pushZero,if_pos hy,hp]

/-- Compact chart functions extend smoothly by the explicit zero extension. -/
theorem pushZero_properties {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : M.Carrier) {φ : ComplexVector n → F}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ chartTarget a) :
    HasCompactSupport (pushZero a φ) ∧
      ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, F) ∞ (pushZero a φ) := by
  letI := realSmooth M
  let Ξ := pushZero a φ
  let K := chartInv a '' tsupport φ
  have hK : IsCompact K := hcφ.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono hsφ)
  have hKs : K ⊆ (extChartAt (ComplexModel n) a).source := by
    rintro _ ⟨z,hz,rfl⟩
    exact (extChartAt (ComplexModel n) a).map_target (hsφ hz)
  have hsupp : Function.support Ξ ⊆ K := by
    intro y hy
    change Ξ y ≠ 0 at hy
    by_cases hys : y ∈ (extChartAt (ComplexModel n) a).source
    · have hφnz : φ (chartPt a y) ≠ 0 := by simpa only [Ξ,pushZero,if_pos hys] using hy
      exact ⟨chartPt a y,subset_closure hφnz,(extChartAt (ComplexModel n) a).left_inv hys⟩
    · exact False.elim (hy (by simp only [Ξ,pushZero,if_neg hys]))
  have htsupp : tsupport Ξ ⊆ K := closure_minimal hsupp hK.isClosed
  have hΞs := htsupp.trans hKs
  refine ⟨hK.of_isClosed_subset (isClosed_tsupport Ξ) htsupp,?_⟩
  apply contMDiff_of_tsupport
  intro y hy
  have hys := hΞs hy
  have hchart := contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := ∞)
    (x := a) (x' := y) (by simpa only [extChartAt_source] using hys)
  have hcomp := hφ.contMDiff.contMDiffAt.comp y hchart
  have hcomp' : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, F) ∞
      (fun p => φ (chartPt a p)) y := by
    change ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, F) ∞
      (φ ∘ extChartAt (ComplexModel n) a) y
    simpa only [real_extChartAt_eq] using hcomp
  apply hcomp'.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := ComplexModel n) a).mem_nhds hys] with p hp
  simp only [Ξ,pushZero,if_pos hp]

theorem cutoff_between_compacts {K T : Set M.Carrier}
    (hK : IsCompact K) (hT : IsCompact T) (hKT : K ⊆ interior T) :
    ∃ β : M.Carrier → ℝ, SmoothFn β ∧ HasCompactSupport β ∧
      (∀ p ∈ K, β p=1) ∧ (∀ p ∉ T, β p=0) ∧ ∀ p, 0 ≤ β p ∧ β p ≤ 1 := by
  letI := realSmooth M
  letI : LocallyCompactSpace M.Carrier := ChartedSpace.locallyCompactSpace (ComplexVector n) M.Carrier
  obtain ⟨p,hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, ComplexVector n)) hK.isClosed (fun _ : Unit => interior T)
    (fun _ => isOpen_interior) (by simpa only [iUnion_const] using hKT)
  have hsupp : tsupport (p ()) ⊆ T := (hp ()).trans interior_subset
  refine ⟨p (),smoothFn_of_contMDiff (p ()).contMDiff,
    hT.of_isClosed_subset (isClosed_tsupport _) hsupp,?_,?_,?_⟩
  · intro y hy
    simpa only [finsum_eq_sum_of_fintype,Fintype.sum_unique] using p.sum_eq_one hy
  · intro y hy
    by_contra hn
    exact hy (hsupp (subset_closure hn))
  · intro y
    exact ⟨p.nonneg () y,p.le_one () y⟩

end Yau.Proofs.SmoothExhaustionAux
