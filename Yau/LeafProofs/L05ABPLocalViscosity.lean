import Yau.LeafProofs.L05ABPViscosityApprox

noncomputable section

open Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem touchAbove_of_eventuallyEq {n : ℕ} {f v phi : Point n → ℝ} {q : Point n}
    (heq : f =ᶠ[𝓝 q] v) (ht : touchAbove phi f q) : touchAbove phi v q := by
  refine ⟨ht.1.trans heq.eq_of_nhds,?_⟩
  filter_upwards [heq,ht.2] with y hy ht
  simpa only [hy] using ht

theorem viscositySub_eqOn_open {n : ℕ} {Q : Set (Point n)}
    {f v g : Point n → ℝ} {G : Sym n → Point n → ℝ}
    (hQ : IsOpen Q) (heq : Set.EqOn f v Q) (hsub : viscositySub Q G g v) :
    viscositySub Q G g f := by
  intro q hq phi hphi ht
  have he : f =ᶠ[𝓝 q] v := by
    filter_upwards [hQ.mem_nhds hq] with y hy
    exact heq hy
  exact hsub q hq phi hphi (touchAbove_of_eventuallyEq he ht)

theorem supRegularize_local_viscosity_jet {n : ℕ}
    {f v phi g : Point n → ℝ} {M epsilon : ℝ}
    {Q : Set (Point n)} {G : Sym n → Point n → ℝ}
    (hf : Continuous f) (hM : 0≤M) (hb : ∀ r, |f r|≤M) (hepsilon : 0<epsilon)
    (hQ : IsOpen Q) (heq : Set.EqOn f v Q) (hsub : viscositySub Q G g v)
    {y q : Point n} (hqQ : q∈Q)
    (hq : supRegularize epsilon f y=f q-qnorm2 (y-q)/(2*epsilon))
    (hphi : ContDiffAt ℝ 2 phi y) (ht : touchAbove phi (supRegularize epsilon f) y) :
    timeD Set.univ phi y-G (hessian phi y) q≤g q :=
  supRegularize_viscosity_jet hf hM hb hepsilon (viscositySub_eqOn_open hQ heq hsub)
    hqQ hq hphi ht

end Yau.LeafProofs.L05Aux
