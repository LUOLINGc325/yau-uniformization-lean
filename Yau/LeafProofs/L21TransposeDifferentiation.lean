import Yau.LeafProofs.L21ScaledComplex
import Yau.LeafProofs.L21WeakLocality

/-! Differentiating the literal formal transpose of a first-order row.
The second coefficient derivatives cancel by Schwarz symmetry. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ} {ι : Type*} [Fintype ι]

def rowDivergence (v : ι → X n) (p : ι → X n → ℂ) (x : X n) : ℂ :=
  ∑ a, fderiv ℝ (p a) x (v a)

def rowTranspose (v : ι → X n) (p : ι → X n → ℂ) (ψ : X n → ℂ) (x : X n) : ℂ :=
  -rowApply v p ψ x - rowDivergence v p x * ψ x

def rowDirectional (p : ι → X n → ℂ) (w : X n) (a : ι) (x : X n) : ℂ :=
  fderiv ℝ (p a) x w

theorem contDiffOn_rowDirectional {O : Set (X n)} (hO : IsOpen O)
    (p : ι → X n → ℂ) (hp : ∀ a, ContDiffOn ℝ ∞ (p a) O) (w : X n) (a : ι) :
    ContDiffOn ℝ ∞ (rowDirectional p w a) O :=
  ((hp a).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_rowDivergence {O : Set (X n)} (hO : IsOpen O)
    (v : ι → X n) (p : ι → X n → ℂ) (hp : ∀ a, ContDiffOn ℝ ∞ (p a) O) :
    ContDiffOn ℝ ∞ (rowDivergence v p) O :=
  ContDiffOn.sum (fun a _ => contDiffOn_rowDirectional hO p hp (v a) a)

theorem contDiffOn_rowTranspose {O : Set (X n)} (hO : IsOpen O)
    (v : ι → X n) (p : ι → X n → ℂ) (hp : ∀ a, ContDiffOn ℝ ∞ (p a) O)
    {ψ : X n → ℂ} (hψ : ContDiffOn ℝ ∞ ψ O) :
    ContDiffOn ℝ ∞ (rowTranspose v p ψ) O :=
  (contDiffOn_real_row_sum hO v p hp hψ).neg.sub ((contDiffOn_rowDivergence hO v p hp).mul hψ)

theorem tsupport_rowTranspose_subset (v : ι → X n) (p : ι → X n → ℂ) (ψ : X n → ℂ) :
    tsupport (rowTranspose v p ψ) ⊆ tsupport ψ := by
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  exact hx (by simp [rowTranspose, rowApply, image_eq_zero_of_notMem_tsupport hn,
    fderiv_of_notMem_tsupport ℝ hn])

def rowTransposeTest {O : Set (X n)} (hO : IsOpen O)
    (v : ι → X n) (p : ι → X n → ℂ) (hp : ∀ a, ContDiffOn ℝ ∞ (p a) O)
    (ψ : CompactTest O) : CompactTest O :=
  ⟨rowTranspose v p ψ,
    Yau.LeafProofs.L14Aux.contDiff_of_contDiffOn_of_tsupport_subset hO _
      (contDiffOn_rowTranspose hO v p hp ψ.property.1.contDiffOn)
      ((tsupport_rowTranspose_subset v p ψ).trans ψ.property.2.2),
    ψ.property.2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_rowTranspose_subset v p ψ),
    (tsupport_rowTranspose_subset v p ψ).trans ψ.property.2.2⟩

theorem fderiv_rowDivergence (v : ι → X n) (p : ι → X n → ℂ) {x : X n}
    (hp : ∀ a, DifferentiableAt ℝ (fderiv ℝ (p a)) x) (w : X n) :
    fderiv ℝ (rowDivergence v p) x w =
      ∑ a, fderiv ℝ (fderiv ℝ (p a)) x w (v a) := by
  have hd (a : ι) : DifferentiableAt ℝ (fun y => fderiv ℝ (p a) y (v a)) x :=
    (hp a).clm_apply (differentiableAt_const (v a))
  change fderiv ℝ (fun y => ∑ a, fderiv ℝ (p a) y (v a)) x w = _
  rw [fderiv_fun_sum (A := fun a y => fderiv ℝ (p a) y (v a)) (fun a _ => hd a), _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact fderiv_directional (hp a) (v a) w

theorem rowTranspose_directional {O : Set (X n)} (hO : IsOpen O)
    (v : ι → X n) (p : ι → X n → ℂ) (hp : ∀ a, ContDiffOn ℝ ∞ (p a) O)
    {ψ : X n → ℂ} (hψ : ContDiffOn ℝ ∞ ψ O) {x : X n} (hx : x ∈ O) (w : X n) :
    fderiv ℝ (rowTranspose v p ψ) x w =
      rowTranspose v p (fun y => fderiv ℝ ψ y w) x +
        rowTranspose v (rowDirectional p w) ψ x := by
  have hpAt (a : ι) := (hp a).contDiffAt (hO.mem_nhds hx)
  have hpD (a : ι) := (hpAt a).differentiableAt (by simp)
  have hpDD (a : ι) := ((hpAt a).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hψAt := hψ.contDiffAt (hO.mem_nhds hx)
  have hψD := hψAt.differentiableAt (by simp)
  have hψDD := (hψAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hR := ((contDiffOn_real_row_sum hO v p hp hψ).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hDiv := ((contDiffOn_rowDivergence hO v p hp).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hsymψ (a : ι) : fderiv ℝ (fderiv ℝ ψ) x w (v a) =
      fderiv ℝ (fderiv ℝ ψ) x (v a) w := (hψAt.isSymmSndFDerivAt (by simp)).eq _ _
  have hsymp (a : ι) : fderiv ℝ (fderiv ℝ (p a)) x w (v a) =
      fderiv ℝ (fderiv ℝ (p a)) x (v a) w := ((hpAt a).isSymmSndFDerivAt (by simp)).eq _ _
  have hpdir (a : ι) : fderiv ℝ (rowDirectional p w a) x (v a) =
      fderiv ℝ (fderiv ℝ (p a)) x (v a) w := fderiv_directional (hpDD a) w (v a)
  change fderiv ℝ (fun y => -rowApply v p ψ y - rowDivergence v p y * ψ y) x w = _
  rw [fderiv_fun_sub (f := fun y => -rowApply v p ψ y)
    (g := fun y => rowDivergence v p y * ψ y) hR.neg (hDiv.mul hψD),
    fderiv_fun_neg, fderiv_fun_mul (c := rowDivergence v p) (d := ψ) hDiv hψD]
  simp only [_root_.sub_apply, _root_.neg_apply, _root_.add_apply, _root_.smul_apply, smul_eq_mul,
    fderiv_rowApply v p hpD hψDD, fderiv_rowDivergence v p hpDD, rowTranspose,
    rowApply, rowDivergence, rowDirectional, fderiv_directional hψDD,
    hpdir, hsymψ, hsymp, Finset.sum_add_distrib, Finset.sum_mul]
  simp only [mul_comm, Finset.mul_sum]
  ring

end Yau.LeafProofs.L21Aux
