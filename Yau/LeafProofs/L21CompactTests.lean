import Yau.LeafProofs.L21WeightedAdjointFormula

/-! The actual common core of smooth compact scalar functions on an open
real-coordinate domain, preserved by the graph operators and their adjoints. -/

open scoped ContDiff Topology
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def compactTestGroup (O : Set (X n)) : AddSubgroup (X n → ℂ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ O}
  zero_mem' := ⟨contDiff_const, by simp [HasCompactSupport], by simp⟩
  add_mem' := by
    rintro f g ⟨hf, hcf, hsf⟩ ⟨hg, hcg, hsg⟩
    exact ⟨hf.add hg, hcf.add hcg, (tsupport_add f g).trans (Set.union_subset hsf hsg)⟩
  neg_mem' := by
    rintro f ⟨hf, hcf, hsf⟩
    exact ⟨hf.neg, hcf.neg, by simpa only [tsupport_neg] using hsf⟩

abbrev CompactTest (O : Set (X n)) := ↥(compactTestGroup O)

instance (O : Set (X n)) : CoeFun (CompactTest O) (fun _ => X n → ℂ) := ⟨Subtype.val⟩

theorem contDiff_of_contDiffOn_tsupport_subset
    {O : Set (X n)} (hO : IsOpen O) {f g : X n → ℂ}
    (hg : ContDiffOn ℝ ∞ g O) (hs : tsupport g ⊆ tsupport f) (hf : tsupport f ⊆ O) :
    ContDiff ℝ ∞ g := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hg.contDiffAt (hO.mem_nhds (hf hx))
  · have hxg : x ∉ tsupport g := fun hh => hx (hs hh)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hxg)

theorem tsupport_dbarA_subset
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (f : X n → ℂ) :
    tsupport (dbarA A i f) ⊆ tsupport f := by
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have hd := fderiv_of_notMem_tsupport ℝ hn
  have hz : dbarA A i f x = 0 := by simp [dbarA, Yau.wirt, Yau.wirtBar, hd]
  exact hx hz

theorem tsupport_weightedDStar_subset
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (φ : X n → ℝ) (i : Fin n) (f : X n → ℂ) :
    tsupport (weightedDStar A φ i f) ⊆ tsupport f := by
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have hd := fderiv_of_notMem_tsupport ℝ hn
  have hf := image_eq_zero_of_notMem_tsupport hn
  have hz : weightedDStar A φ i f x = 0 := by
    simp only [weightedDStar, conjugateD, hd, _root_.zero_apply, mul_zero,
      Finset.sum_const_zero, neg_zero, hf, add_zero]
  exact hx hz

theorem contDiffOn_real_row_sum {ι : Type*} [Fintype ι]
    {O : Set (X n)} (hO : IsOpen O) (v : ι → X n) (p : ι → X n → ℂ)
    (hp : ∀ a, ContDiffOn ℝ ∞ (p a) O) {f : X n → ℂ} (hf : ContDiffOn ℝ ∞ f O) :
    ContDiffOn ℝ ∞ (fun x => ∑ a, p a x * fderiv ℝ f x (v a)) O := by
  have hdf := hf.fderiv_of_isOpen hO (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  exact ContDiffOn.sum (fun a _ => (hp a).mul (hdf.clm_apply contDiffOn_const))

theorem contDiffOn_dbarA
    {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (i : Fin n) {f : X n → ℂ} (hf : ContDiffOn ℝ ∞ f O) :
    ContDiffOn ℝ ∞ (dbarA A i f) O := by
  have hh := contDiffOn_real_row_sum hO Yau.realVec (dbarRealCoefficient A i)
    (fun a => dbarRealCoefficient_smoothOn hA i a) hf
  exact hh.congr (fun x _ => dbarA_eq_real_rows A i f x)

theorem contDiffOn_weightedDStar
    {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O)
    (i : Fin n) {f : X n → ℂ} (hf : ContDiffOn ℝ ∞ f O) :
    ContDiffOn ℝ ∞ (weightedDStar A φ i f) O := by
  have hp (a : Yau.RIdx n) :
      ContDiffOn ℝ ∞ (fun y => star (dbarRealCoefficient A i a y)) O :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (dbarRealCoefficient_smoothOn hA i a)
  have hconj (g : X n → ℂ) (hg : ContDiffOn ℝ ∞ g O) :
      ContDiffOn ℝ ∞ (conjugateD A i g) O := contDiffOn_real_row_sum hO Yau.realVec _ hp hg
  have hdiv : ContDiffOn ℝ ∞ (conjugateDivergence A i) O :=
    ContDiffOn.sum (fun a _ =>
      ((hp a).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const)
  exact (hconj f hf).neg.add
    (((hconj (fun y => (φ y : ℂ)) (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ)).sub hdiv).mul hf)

theorem dbarA_add
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    {f g : X n → ℂ} {x : X n} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dbarA A i (f + g) x = dbarA A i f x + dbarA A i g x := by
  simp only [dbarA_eq_real_rows, fderiv_add hf hg, _root_.add_apply,
    mul_add, Finset.sum_add_distrib]

theorem weightedDStar_add
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (φ : X n → ℝ) (i : Fin n)
    {f g : X n → ℂ} {x : X n} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    weightedDStar A φ i (f + g) x = weightedDStar A φ i f x + weightedDStar A φ i g x := by
  simp only [weightedDStar, conjugateD, fderiv_add hf hg, _root_.add_apply,
    Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

def testD {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O) (i : Fin n) :
    CompactTest O →+ CompactTest O where
  toFun f := ⟨dbarA A i f, contDiff_of_contDiffOn_tsupport_subset hO
    (contDiffOn_dbarA hO hA i f.property.1.contDiffOn) (tsupport_dbarA_subset A i f) f.property.2.2,
    f.property.2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_dbarA_subset A i f),
    (tsupport_dbarA_subset A i f).trans f.property.2.2⟩
  map_zero' := Subtype.ext (by funext x; simp [dbarA, Yau.wirt, Yau.wirtBar])
  map_add' f g := Subtype.ext (by
    funext x
    exact dbarA_add A i (f.property.1.differentiable (by simp) x)
      (g.property.1.differentiable (by simp) x))

def testDs {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O) (i : Fin n) :
    CompactTest O →+ CompactTest O where
  toFun f := ⟨weightedDStar A φ i f, contDiff_of_contDiffOn_tsupport_subset hO
    (contDiffOn_weightedDStar hO hA hφ i f.property.1.contDiffOn)
      (tsupport_weightedDStar_subset A φ i f) f.property.2.2,
    f.property.2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_weightedDStar_subset A φ i f),
    (tsupport_weightedDStar_subset A φ i f).trans f.property.2.2⟩
  map_zero' := Subtype.ext (by funext x; simp [weightedDStar, conjugateD])
  map_add' f g := Subtype.ext (by
    funext x
    exact weightedDStar_add A φ i (f.property.1.differentiable (by simp) x)
      (g.property.1.differentiable (by simp) x))

end Yau.LeafProofs.L21Aux
