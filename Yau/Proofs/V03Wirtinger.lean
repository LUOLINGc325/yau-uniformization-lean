import Yau.Proofs.V03Energy

/-! Locality and addition for the actual totalized mixed derivative. These
facts justify using identities valid on a neighborhood of the parameter 0. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

theorem wirtBar_add {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f g : V → ℂ) (z v : V)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtBar (fun y => f y + g y) z v = wirtBar f z v + wirtBar g z v := by
  unfold wirtBar
  rw [fderiv_fun_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

theorem wirt_add {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f g : V → ℂ) (z v : V)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirt (fun y => f y + g y) z v = wirt f z v + wirt g z v := by
  unfold wirt
  rw [fderiv_fun_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

theorem wirtBar_differentiableAt {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] {f : V → ℂ} {z : V}
    (hf : ContDiffAt ℝ 2 f z) (v : V) :
    DifferentiableAt ℝ (fun y => wirtBar f y v) z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) z :=
    hd.clm_apply (differentiableAt_const v)
  have h2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Complex.I • v)) z :=
    hd.clm_apply (differentiableAt_const (Complex.I • v))
  exact (h1.add (h2.const_mul Complex.I)).const_mul (1 / 2 : ℂ)

theorem mixedReal_congr {f g : ℂ → ℝ} (hfg : f =ᶠ[𝓝 0] g) :
    mixedReal f = mixedReal g := by
  have hc : (fun z => (f z : ℂ)) =ᶠ[𝓝 (0 : ℂ)] (fun z => (g z : ℂ)) :=
    hfg.mono fun z hz => congrArg (fun t : ℝ => (t : ℂ)) hz
  have hd : fderiv ℝ (fun z => (f z : ℂ)) =ᶠ[𝓝 (0 : ℂ)]
      fderiv ℝ (fun z => (g z : ℂ)) := hc.fderiv
  have hb : (fun z => wirtBar (fun z' => (f z' : ℂ)) z 1) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => wirtBar (fun z' => (g z' : ℂ)) z 1) :=
    hd.mono fun z hz => by simp only [wirtBar, hz]
  unfold mixedReal wirt
  rw [hb.fderiv_eq]

theorem mixedReal_add {f g : ℂ → ℝ}
    (hf : ContDiffAt ℝ 2 (fun z => (f z : ℂ)) 0)
    (hg : ContDiffAt ℝ 2 (fun z => (g z : ℂ)) 0) :
    mixedReal (fun z => f z + g z) = mixedReal f + mixedReal g := by
  have he : (fun z => wirtBar (fun z' => ((f z' + g z' : ℝ) : ℂ)) z 1)
      =ᶠ[𝓝 (0 : ℂ)]
      (fun z => wirtBar (fun z' => (f z' : ℂ)) z 1 +
        wirtBar (fun z' => (g z' : ℂ)) z 1) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)]
      with z hfz hgz
    simp only [Complex.ofReal_add]
    exact wirtBar_add _ _ z 1 (hfz.differentiableAt (by norm_num))
      (hgz.differentiableAt (by norm_num))
  have hw : wirt (fun z => wirtBar (fun z' => ((f z' + g z' : ℝ) : ℂ)) z 1) 0 1 =
      wirt (fun z => wirtBar (fun z' => (f z' : ℂ)) z 1) 0 1 +
      wirt (fun z => wirtBar (fun z' => (g z' : ℂ)) z 1) 0 1 := by
    unfold wirt
    rw [he.fderiv_eq,
      fderiv_fun_add (wirtBar_differentiableAt hf 1) (wirtBar_differentiableAt hg 1)]
    simp only [ContinuousLinearMap.add_apply]
    ring
  exact congrArg Complex.re hw

theorem mixedReal_add_const (f : ℂ → ℝ) (c : ℝ) :
    mixedReal (fun z => f z + c) = mixedReal f := by
  unfold mixedReal wirtBar
  simp only [Complex.ofReal_add, fderiv_add_const]

end Yau.Blueprint.V03Proof
