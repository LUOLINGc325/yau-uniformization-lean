import Yau.LeafProofs.L05ABPRegularization
import Yau.LeafProofs.L05ABPGeometry

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem spatialD_translate {n : ℕ} (phi : Point n → ℝ) (a : Point n) (c : ℝ) (z : Point n) :
    spatialD (fun q => phi (q+a)+c) z = spatialD phi (z+a) := by
  change fderiv ℝ (fun x => phi (x+a.1,z.2+a.2)+c) z.1 =
    fderiv ℝ (fun x => phi (x,z.2+a.2)) (z.1+a.1)
  rw [fderiv_add_const]
  exact fderiv_comp_add_right (𝕜 := ℝ) (f := fun x => phi (x,z.2+a.2)) a.1

theorem spatialDD_translate {n : ℕ} (phi : Point n → ℝ) (a : Point n) (c : ℝ) (z : Point n) :
    spatialDD (fun q => phi (q+a)+c) z = spatialDD phi (z+a) := by
  change fderiv ℝ (fun x => spatialD (fun q => phi (q+a)+c) (x,z.2)) z.1 = _
  simp_rw [spatialD_translate]
  change fderiv ℝ (fun x => spatialD phi (x+a.1,z.2+a.2)) z.1 =
    fderiv ℝ (fun x => spatialD phi (x,z.2+a.2)) (z.1+a.1)
  exact fderiv_comp_add_right (𝕜 := ℝ) (f := fun x => spatialD phi (x,z.2+a.2)) a.1

theorem hessian_translate {n : ℕ} (phi : Point n → ℝ) (a : Point n) (c : ℝ) (z : Point n) :
    hessian (fun q => phi (q+a)+c) z = hessian phi (z+a) := by
  simp only [hessian,spatialDD_translate]

theorem timeD_translate {n : ℕ} (phi : Point n → ℝ) (a : Point n) (c : ℝ) (z : Point n) :
    timeD Set.univ (fun q => phi (q+a)+c) z = timeD Set.univ phi (z+a) := by
  simp only [timeD,Set.mem_univ,Set.ofPred_true,derivWithin_univ]
  change deriv (fun t => phi (z.1+a.1,t+a.2)+c) z.2 =
    deriv (fun t => phi (z.1+a.1,t)) (z.2+a.2)
  rw [deriv_add_const]
  exact deriv_comp_add_const (fun t => phi (z.1+a.1,t)) a.2 z.2

theorem upper_touch_translate_of_comparison {E : Type*} [NormedAddCommGroup E]
    {v U phi : E → ℝ} {y q : E} {c : ℝ} (hq : U y=v q-c)
    (hcompare : ∀ r, v r-c ≤ U (r+(y-q)))
    (ht : phi y=U y ∧ ∀ᶠ r in 𝓝 y, U r ≤ phi r) :
    (phi (q+(y-q))+c=v q) ∧ ∀ᶠ r in 𝓝 q, v r ≤ phi (r+(y-q))+c := by
  have hqy : q+(y-q)=y := by abel
  have hmap : Tendsto (fun r : E => r+(y-q)) (𝓝 q) (𝓝 y) := by
    have hc : Continuous (fun r : E => r+(y-q)) := continuous_id.add continuous_const
    simpa only [hqy] using hc.tendsto q
  refine ⟨?_,?_⟩
  · rw [hqy,ht.1,hq]
    exact sub_add_cancel _ _
  · filter_upwards [hmap ht.2] with r hr
    change U (r+(y-q)) ≤ phi (r+(y-q)) at hr
    exact (sub_le_iff_le_add).mp ((hcompare r).trans hr)

theorem supRegularize_upper_touch {n : ℕ} {v phi : Point n → ℝ} {B epsilon : ℝ}
    (hv : Continuous v) (hB : 0 ≤ B) (hb : ∀ r, |v r| ≤ B) (hepsilon : 0 < epsilon)
    {y q : Point n}
    (hq : supRegularize epsilon v y = v q-qnorm2 (y-q)/(2*epsilon))
    (ht : touchAbove phi (supRegularize epsilon v) y) :
    touchAbove (fun r => phi (r+(y-q))+qnorm2 (y-q)/(2*epsilon)) v q := by
  apply upper_touch_translate_of_comparison hq _ ht
  intro r
  have hc := le_supRegularize hv hB hb hepsilon (r+(y-q)) r
  have he : (r+(y-q))-r=y-q := by abel
  rw [he] at hc
  exact hc

theorem supRegularize_viscosity_jet {n : ℕ} {v phi g : Point n → ℝ} {B epsilon : ℝ}
    {Q : Set (Point n)} {G : Sym n → Point n → ℝ}
    (hv : Continuous v) (hB : 0 ≤ B) (hb : ∀ r, |v r| ≤ B) (hepsilon : 0 < epsilon)
    (hsub : viscositySub Q G g v) {y q : Point n} (hqQ : q ∈ Q)
    (hq : supRegularize epsilon v y = v q-qnorm2 (y-q)/(2*epsilon))
    (hphi : ContDiffAt ℝ 2 phi y) (ht : touchAbove phi (supRegularize epsilon v) y) :
    timeD Set.univ phi y-G (hessian phi y) q ≤ g q := by
  have hqy : q+(y-q)=y := by abel
  have hs : ContDiffAt ℝ 2
      (fun r => phi (r+(y-q))+qnorm2 (y-q)/(2*epsilon)) q := by
    have hc : ContDiffAt ℝ 2 phi (q+(y-q)) := by simpa only [hqy] using hphi
    have ha : ContDiffAt ℝ 2 (fun r : Point n => r+(y-q)) q := by fun_prop
    have hh : ContDiffAt ℝ 2 (fun r => phi (r+(y-q))) q := hc.comp q ha
    exact hh.add contDiffAt_const
  have ht' := supRegularize_upper_touch hv hB hb hepsilon hq ht
  have hi := hsub q hqQ _ hs ht'
  rw [timeD_translate,hessian_translate,hqy] at hi
  exact hi

end Yau.LeafProofs.L05Aux
