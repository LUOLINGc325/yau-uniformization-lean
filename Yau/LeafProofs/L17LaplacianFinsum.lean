import Yau.LeafProofs.L17HessianFinsum
import Yau.LeafProofs.L17ParabolicOperatorRegularity

/-! The original scalar Laplacian passes through a genuinely locally finite sum. -/

open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open L17ParabolicOperatorAux L17LocalizedSchauderAux

theorem realHessianContraction_finsum {ι : Type*} {n : ℕ} (a : Matrix (RIdx n) (RIdx n) ℝ)
    (f : ι → ComplexVector n → ℝ) (I : Finset ι) {x : ComplexVector n}
    (hf : ∀ i ∈ I, ContDiffAt ℝ 2 (f i) x)
    (hzero : ∀ᶠ z in 𝓝 x, ∀ i, i ∉ I → f i z = 0) :
    realHessianContraction a (fun z => ∑ᶠ i,f i z) x = ∑ᶠ i,realHessianContraction a (f i) x := by
  classical
  have hZero (i : ι) (hi : i ∉ I) : fderiv ℝ (fderiv ℝ (f i)) x = 0 := by
    have he : f i =ᶠ[𝓝 x] (fun _ => 0) := hzero.mono (fun z hz => hz i hi)
    simpa using ((he.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ))
  have hFinite : (Function.support (fun i => fderiv ℝ (fderiv ℝ (f i)) x)).Finite :=
    I.finite_toSet.subset (fun i hi => by by_contra hn; exact hi (hZero i hn))
  have hMap := (hessianContractionCLM n a).toAddMonoidHom.map_finsum hFinite
  change hessianContractionCLM n a (∑ᶠ i,fderiv ℝ (fderiv ℝ (f i)) x) =
    ∑ᶠ i,hessianContractionCLM n a (fderiv ℝ (fderiv ℝ (f i)) x) at hMap
  rw [← hessianContractionCLM_eq_actual,secondFDeriv_finsum f I hf hzero]
  simpa only [hessianContractionCLM_eq_actual] using hMap

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem realHessianContraction_congr_of_eventuallyEq {f h : ComplexVector n → ℝ}
    {z : ComplexVector n} (heq : f =ᶠ[𝓝 z] h) (a : Matrix (RIdx n) (RIdx n) ℝ) :
    realHessianContraction a f z = realHessianContraction a h z := by
  simp only [realHessianContraction,((heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ))]

theorem laplacian_zero_of_background_zero
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (f : M.Carrier → ℝ) {z : ComplexVector n} (hz : z ∈ e.source)
    (hzero : (fun w => f (e w)) =ᶠ[𝓝 z] (fun _ => 0)) : laplacian g f (e z) = 0 := by
  have hBg : ContDiffAt ℝ 2 (fun w => f (e w)) z := contDiffAt_const.congr_of_eventuallyEq hzero
  have hNative := native_contDiffAt_of_background e hei f hz hBg
  rw [laplacian_eq_backgroundChart_scalarSymbol g e he hei f hz hNative,
    realHessianContraction_congr_of_eventuallyEq hzero]
  simp only [realHessianContraction,fderiv_fun_const,fderiv_zero,Pi.zero_apply,zero_apply,mul_zero,Finset.sum_const_zero]

theorem laplacian_finsum_background {ι : Type*}
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (f : ι → M.Carrier → ℝ) (I : Finset ι) {z : ComplexVector n} (hz : z ∈ e.source)
    (hf : ∀ i, ContDiffAt ℝ 2 (fun w => f i (e w)) z)
    (hzero : ∀ᶠ w in 𝓝 z, ∀ i, i ∉ I → f i (e w) = 0) :
    laplacian g (fun x => ∑ᶠ i,f i x) (e z) = ∑ᶠ i,laplacian g (f i) (e z) := by
  have hSum : ContDiffAt ℝ 2 (fun w => ∑ᶠ i,f i (e w)) z :=
    contDiffAt_finsum (fun i w => f i (e w)) I 2 (fun i _ => hf i) hzero
  have hNative := native_contDiffAt_of_background e hei (fun x => ∑ᶠ i,f i x) hz hSum
  have hLap (i : ι) := laplacian_eq_backgroundChart_scalarSymbol g e he hei (f i) hz
    (native_contDiffAt_of_background e hei (f i) hz (hf i))
  rw [laplacian_eq_backgroundChart_scalarSymbol g e he hei _ hz hNative,
    realHessianContraction_finsum _ (fun i w => f i (e w)) I (fun i _ => hf i) hzero]
  exact finsum_congr (fun i => (hLap i).symm)

end Yau.LeafProofs.L17Aux
