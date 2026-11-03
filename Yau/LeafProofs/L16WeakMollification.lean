import Yau.LeafProofs.L16WeakLocalization
import Yau.LeafProofs.L03

open MeasureTheory Filter
open scoped Topology ContDiff Convolution
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

instance pointVolume_isAddHaarMeasure {n : ℕ} : (volume : Measure (Point n)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

theorem weak_directionalDerivative_convolution {n : ℕ}
    {u g : Point n → ℝ} (hu : Integrable u volume) (e : Point n)
    (hWeak : ∀ φ : Point n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, u p*fderiv ℝ φ p e) = -(∫ p, g p*φ p))
    (ρ : Point n → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (p : Point n) :
    fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) p e =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) p := by
  have hSystem : Yau.LeafProofs.L03.firstOrderSystemWeakEquation volume
      (fun _ : Unit => e)
      (fun (_ : Unit) (_ : Unit) (_ : Unit) (_ : Point n) => (1 : ℝ))
      (fun (_ : Unit) (_ : Unit) (_ : Point n) => (0 : ℝ))
      (fun (p : Point n) (_ : Unit) => u p) (fun (p : Point n) (_ : Unit) => g p) := by
    intro r φ hφ hcφ
    have h := hWeak φ hφ hcφ
    simp only [Fintype.sum_unique,fderiv_fun_const,Pi.zero_apply,zero_apply,
      one_mul,zero_mul,mul_zero,add_zero,integral_zero] at *
    simp only [mul_comm] at h ⊢
    linarith
  have h := Yau.LeafProofs.L03.firstOrderSystemWeakEquation_mollifier_identity volume
    (fun _ : Unit => e)
    (fun (_ : Unit) (_ : Unit) (_ : Unit) (_ : Point n) => (1 : ℝ))
    (fun (_ : Unit) (_ : Unit) (_ : Point n) => (0 : ℝ))
    (fun _ _ _ => contDiff_const) (fun _ _ _ => (0 : NNReal))
    (fun _ _ _ => LipschitzWith.const _)
    (fun (p : Point n) (_ : Unit) => u p) (fun (p : Point n) (_ : Unit) => g p)
    (fun _ => hu) hSystem ρ hρ hcρ () p
  simp only [Fintype.sum_unique,one_mul,zero_mul,add_zero,sub_self,
    Yau.LeafProofs.L03.friedrichsCommutatorKernel,fderiv_fun_const,Pi.zero_apply,
    zero_apply,mul_zero,integral_zero,zero_add] at h
  simp only [MeasureTheory.convolution_lsmul,smul_eq_mul,mul_zero,integral_zero,sub_zero] at h
  exact sub_eq_zero.mp h

def jointMollifierBump (n : ℕ) : ContDiffBump (0 : Point n) :=
  ⟨1,2,by norm_num,by norm_num⟩

def jointMollifierKernel (n : ℕ) : Point n → ℝ := (jointMollifierBump n).normed volume

def jointMollifierScaled {n : ℕ} (ε : ℝ) : Point n → ℝ :=
  Yau.LeafProofs.L03.rescaledFriedrichsMollifier (jointMollifierKernel n) ε

def jointMollify {n : ℕ} (ε : ℝ) (u : Point n → ℝ) : Point n → ℝ :=
  jointMollifierScaled ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u

theorem jointMollifierKernel_smooth (n : ℕ) : ContDiff ℝ ∞ (jointMollifierKernel n) :=
  (jointMollifierBump n).contDiff_normed

theorem jointMollifierKernel_compact (n : ℕ) : HasCompactSupport (jointMollifierKernel n) :=
  (jointMollifierBump n).hasCompactSupport_normed

theorem jointMollifierKernel_nonneg {n : ℕ} (p : Point n) : 0 ≤ jointMollifierKernel n p :=
  (jointMollifierBump n).nonneg_normed p

theorem jointMollifierKernel_mass (n : ℕ) : (∫ p, jointMollifierKernel n p) = 1 :=
  (jointMollifierBump n).integral_normed

theorem jointMollifierScaled_smooth {n : ℕ} (ε : ℝ) : ContDiff ℝ ∞ (jointMollifierScaled (n := n) ε) :=
  Yau.LeafProofs.L03.rescaledFriedrichsMollifier_contDiff_top _ ε (jointMollifierKernel_smooth n)

theorem jointMollifierScaled_compact {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (jointMollifierScaled (n := n) ε) :=
  Yau.LeafProofs.L03.rescaledFriedrichsMollifier_compact _ hε.ne' (jointMollifierKernel_compact n)

theorem jointMollifierScaled_nonneg {n : ℕ} {ε : ℝ} (hε : 0 < ε) (p : Point n) :
    0 ≤ jointMollifierScaled (n := n) ε p :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _)) (jointMollifierKernel_nonneg _)

theorem jointMollifierScaled_mass {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    (∫ p, jointMollifierScaled (n := n) ε p) = 1 := by
  exact (Yau.LeafProofs.L03.rescaledFriedrichsMollifier_integral volume _ hε).trans
    (jointMollifierKernel_mass n)

theorem jointMollify_smooth {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    {u : Point n → ℝ} (hu : Integrable u volume) : ContDiff ℝ ∞ (jointMollify ε u) :=
  (jointMollifierScaled_compact hε).contDiff_convolution_left _
    (jointMollifierScaled_smooth ε) hu.locallyIntegrable

theorem jointMollify_memLp {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    {u : Point n → ℝ} (hu : MemLp u 2 volume) (hcu : HasCompactSupport u) :
    MemLp (jointMollify ε u) 2 volume := by
  have h1 := Yau.LeafProofs.L03.memLp_two_compact_integrable volume u hu hcu
  have h2 := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  exact (Yau.LeafProofs.L03.probability_convolution_L2_bound volume _
    (jointMollifierScaled_nonneg hε) (jointMollifierScaled_mass hε) u h1 h2).1

theorem jointMollify_L2_tendsto {n : ℕ} {ε : ℕ → ℝ}
    (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1) (hLim : Tendsto ε atTop (𝓝 0))
    {u : Point n → ℝ} (hu : MemLp u 2 volume) (hcu : HasCompactSupport u) :
    Tendsto (fun k => ∫ p, ‖jointMollify (ε k) u p-u p‖^2) atTop (𝓝 0) :=
  Yau.LeafProofs.L03.rescaledFriedrichsMollifier_convolution_L2_tendsto_of_memLp
    volume _ ((jointMollifierKernel_smooth n).of_le (by simp))
    (jointMollifierKernel_compact n) jointMollifierKernel_nonneg (jointMollifierKernel_mass n)
    ε hε hε1 hLim u hu hcu

theorem jointMollify_L2_contract {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    {u : Point n → ℝ} (hu : MemLp u 2 volume) (hcu : HasCompactSupport u) :
    (∫ p, ‖jointMollify ε u p‖^2) ≤ ∫ p, ‖u p‖^2 := by
  have h1 := Yau.LeafProofs.L03.memLp_two_compact_integrable volume u hu hcu
  have h2 := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  exact (Yau.LeafProofs.L03.probability_convolution_L2_bound volume _
    (jointMollifierScaled_nonneg hε) (jointMollifierScaled_mass hε) u h1 h2).2

theorem weakGradient_jointMollify_spatial {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hu : Integrable u volume) (hG : WeakGradient Set.univ Set.univ u G)
    (p : Point n) (i : Yau.RIdx n) :
    d (fun x => jointMollify ε u (x,p.2)) p.1 i = jointMollify ε (fun q => G q i) p := by
  rw [d_eq_joint_fderiv ((jointMollify_smooth hε hu).differentiable (by simp) p) i]
  apply weak_directionalDerivative_convolution hu (Yau.realVec i,0) ?_
    (jointMollifierScaled ε) (jointMollifierScaled_smooth ε) (jointMollifierScaled_compact hε) p
  intro φ hφ hcφ
  have h := hG φ ⟨hφ,hcφ,by simp only [Set.univ_prod_univ]; exact Set.subset_univ _⟩ i
  rw [productVolume_eq_restrict] at h
  simp only [Set.univ_prod_univ,Measure.restrict_univ] at h
  simpa only [d_eq_joint_fderiv (hφ.differentiable (by simp) _) i] using h

theorem localEnergy_cutoff_jointMollify_spatial {n : ℕ} {O : Set (Space n)} {l r ε : ℝ}
    (hO : IsOpen O) (hε : 0 < ε) {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G) {η : Point n → ℝ}
    (hη : Test (O ×ˢ Set.Ioo l r) η) (p : Point n) (i : Yau.RIdx n) :
    d (fun x => jointMollify ε (fun q => η q*u q) (x,p.2)) p.1 i =
      jointMollify ε (fun q => η q*G q i+u q*d (fun x => η (x,q.2)) q.1 i) p := by
  have hL1 := (localEnergy_cutoff_integrable hO hE hη.1.continuous hη.2.1 hη.2.2).1
  have hWeak := (localEnergy_cutoff_weakH1 hO hE hη).2.2
  exact weakGradient_jointMollify_spatial hε hL1 hWeak p i

end Yau.LeafProofs.L16Aux
