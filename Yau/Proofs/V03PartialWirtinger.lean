import Yau.Proofs.V03PartialDerivative
import Yau.Proofs.V03LeviMatrix

/-! Actual spatial Wirtinger Hessians depend smoothly on parameters up to
one-sided parameter boundaries. Joint within derivatives supply a native
representative; the open spatial factor supplies the ordinary derivatives. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def spatialWirtBar (f : E × P → ℂ) (S : Set E) (J : Set P) (v : E) (p : E × P) : ℂ :=
  (1 / 2 : ℂ) * (fderivWithin ℝ f (S ×ˢ J) p (v, 0) +
    Complex.I * fderivWithin ℝ f (S ×ˢ J) p (Complex.I • v, 0))

def spatialWirt (f : E × P → ℂ) (S : Set E) (J : Set P) (v : E) (p : E × P) : ℂ :=
  (1 / 2 : ℂ) * (fderivWithin ℝ f (S ×ˢ J) p (v, 0) -
    Complex.I * fderivWithin ℝ f (S ×ˢ J) p (Complex.I • v, 0))

theorem spatialWirtBar_contDiffOn {S : Set E} {J : Set P} {f : E × P → ℂ}
    (hSJ : UniqueDiffOn ℝ (S ×ˢ J)) (hf : ContDiffOn ℝ ∞ f (S ×ˢ J)) (v : E) :
    ContDiffOn ℝ ∞ (spatialWirtBar f S J v) (S ×ˢ J) :=
  contDiffOn_const.mul ((partialFDeriv_contDiffOn hSJ hf v).add
    (contDiffOn_const.mul (partialFDeriv_contDiffOn hSJ hf (Complex.I • v))))

theorem spatialWirt_contDiffOn {S : Set E} {J : Set P} {f : E × P → ℂ}
    (hSJ : UniqueDiffOn ℝ (S ×ˢ J)) (hf : ContDiffOn ℝ ∞ f (S ×ˢ J)) (v : E) :
    ContDiffOn ℝ ∞ (spatialWirt f S J v) (S ×ˢ J) :=
  contDiffOn_const.mul ((partialFDeriv_contDiffOn hSJ hf v).sub
    (contDiffOn_const.mul (partialFDeriv_contDiffOn hSJ hf (Complex.I • v))))

theorem wirtBar_spatial_slice {S : Set E} (hS : IsOpen S) {J : Set P}
    {f : E × P → ℂ} {p : E × P} (hp : p ∈ S ×ˢ J)
    (hf : DifferentiableWithinAt ℝ f (S ×ˢ J) p) (v : E) :
    wirtBar (fun x => f (x, p.2)) p.1 v = spatialWirtBar f S J v p := by
  simp only [wirtBar, spatialWirtBar,
    fderiv_spatial_slice hS hp.1 hp.2 hf]

theorem wirt_spatial_slice {S : Set E} (hS : IsOpen S) {J : Set P}
    {f : E × P → ℂ} {p : E × P} (hp : p ∈ S ×ˢ J)
    (hf : DifferentiableWithinAt ℝ f (S ×ˢ J) p) (v : E) :
    wirt (fun x => f (x, p.2)) p.1 v = spatialWirt f S J v p := by
  simp only [wirt, spatialWirt,
    fderiv_spatial_slice hS hp.1 hp.2 hf]

theorem mixedWirt_spatial_slice {S : Set E} (hS : IsOpen S) {J : Set P}
    {f : E × P → ℂ} (hSJ : UniqueDiffOn ℝ (S ×ˢ J))
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ J)) {p : E × P} (hp : p ∈ S ×ˢ J) (v w : E) :
    wirt (fun y => wirtBar (fun x => f (x, p.2)) y v) p.1 w =
      spatialWirt (spatialWirtBar f S J v) S J w p := by
  have heq : (fun y => wirtBar (fun x => f (x, p.2)) y v) =ᶠ[𝓝 p.1]
      (fun y => spatialWirtBar f S J v (y, p.2)) := by
    filter_upwards [hS.mem_nhds hp.1] with y hy
    exact wirtBar_spatial_slice (f := f) (p := (y, p.2)) hS ⟨hy, hp.2⟩
      ((hf.differentiableOn (by simp)) (y, p.2) ⟨hy, hp.2⟩) v
  have hbar := spatialWirtBar_contDiffOn hSJ hf v
  have hh := wirt_spatial_slice hS hp ((hbar.differentiableOn (by simp)) p hp) w
  unfold wirt at hh ⊢
  rw [heq.fderiv_eq]
  exact hh

theorem leviMatrix_parameter_contDiffOn {ι : Type*} {S : Set E} (hS : IsOpen S)
    {J : Set P} {f : E × P → ℝ} (hSJ : UniqueDiffOn ℝ (S ×ˢ J))
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ J)) (dir : ι → E) (a b : ι) :
    ContDiffOn ℝ ∞ (fun p : E × P => leviMatrix (fun x => f (x, p.2)) p.1 dir a b)
      (S ×ˢ J) := by
  have hF : ContDiffOn ℝ ∞ (fun p => (f p : ℂ)) (S ×ˢ J) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hf
  have hh := spatialWirt_contDiffOn hSJ (spatialWirtBar_contDiffOn hSJ hF (dir a)) (dir b)
  apply hh.congr
  intro p hp
  exact mixedWirt_spatial_slice hS hSJ hF hp (dir a) (dir b)

end Yau.Blueprint.V03Proof
