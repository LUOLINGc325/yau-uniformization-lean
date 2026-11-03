import Yau.LeafProofs.L05ABPLocalViscosity
import Yau.LeafProofs.L05ABPSemiconvexABP

noncomputable section

open Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem touchAbove_of_local_le {n : ℕ} {phi u v : Point n → ℝ} {p : Point n}
    (hp : u p=v p) (hle : ∀ᶠ q in 𝓝 p, u q≤v q) (ht : touchAbove phi v p) :
    touchAbove phi u p := by
  refine ⟨ht.1.trans hp.symm,?_⟩
  filter_upwards [hle,ht.2] with q hq hqt
  exact hq.trans hqt

theorem touchBelow_of_local_le {n : ℕ} {phi u v : Point n → ℝ} {p : Point n}
    (hp : u p=v p) (hle : ∀ᶠ q in 𝓝 p, v q≤u q) (ht : touchBelow phi v p) :
    touchBelow phi u p := by
  refine ⟨ht.1.trans hp.symm,?_⟩
  filter_upwards [hle,ht.2] with q hq hqt
  exact hqt.trans hq

theorem viscositySub_max {n : ℕ} {Q : Set (Point n)} {G : Sym n → Point n → ℝ}
    {g u v : Point n → ℝ} (hu : viscositySub Q G g u) (hv : viscositySub Q G g v) :
    viscositySub Q G g (fun p => max (u p) (v p)) := by
  intro p hp phi hphi ht
  by_cases h : v p≤u p
  · apply hu p hp phi hphi
    exact touchAbove_of_local_le (max_eq_left h).symm
      (Filter.Eventually.of_forall (fun q => le_max_left (u q) (v q))) ht
  · apply hv p hp phi hphi
    exact touchAbove_of_local_le (max_eq_right (le_of_not_ge h)).symm
      (Filter.Eventually.of_forall (fun q => le_max_right (u q) (v q))) ht

theorem viscositySuper_min {n : ℕ} {Q : Set (Point n)} {G : Sym n → Point n → ℝ}
    {g u v : Point n → ℝ} (hu : viscositySuper Q G g u) (hv : viscositySuper Q G g v) :
    viscositySuper Q G g (fun p => min (u p) (v p)) := by
  intro p hp phi hphi ht
  by_cases h : u p≤v p
  · apply hu p hp phi hphi
    exact touchBelow_of_local_le (min_eq_left h).symm
      (Filter.Eventually.of_forall (fun q => min_le_left (u q) (v q))) ht
  · apply hv p hp phi hphi
    exact touchBelow_of_local_le (min_eq_right (le_of_not_ge h)).symm
      (Filter.Eventually.of_forall (fun q => min_le_right (u q) (v q))) ht

theorem viscositySub_mono_domain {n : ℕ} {Q D : Set (Point n)} {G : Sym n → Point n → ℝ}
    {g u : Point n → ℝ} (hu : viscositySub Q G g u) (hD : D⊆Q) : viscositySub D G g u :=
  fun p hp => hu p (hD hp)

theorem viscositySuper_mono_domain {n : ℕ} {Q D : Set (Point n)} {G : Sym n → Point n → ℝ}
    {g u : Point n → ℝ} (hu : viscositySuper Q G g u) (hD : D⊆Q) : viscositySuper D G g u :=
  fun p hp => hu p (hD hp)

theorem viscositySub_mono_source {n : ℕ} {Q : Set (Point n)} {G : Sym n → Point n → ℝ}
    {f g u : Point n → ℝ} (hu : viscositySub Q G f u) (hfg : ∀ p∈Q, f p≤g p) :
    viscositySub Q G g u := by
  intro p hp phi hphi ht
  exact (hu p hp phi hphi ht).trans (hfg p hp)

theorem viscositySuper_mono_source {n : ℕ} {Q : Set (Point n)} {G : Sym n → Point n → ℝ}
    {f g u : Point n → ℝ} (hu : viscositySuper Q G f u) (hgf : ∀ p∈Q, g p≤f p) :
    viscositySuper Q G g u := by
  intro p hp phi hphi ht
  exact (hgf p hp).trans (hu p hp phi hphi ht)

theorem viscositySub_add_const {n : ℕ} {Q : Set (Point n)} {G : Sym n → Point n → ℝ}
    {g u : Point n → ℝ} (hu : viscositySub Q G g u) (c : ℝ) :
    viscositySub Q G g (fun p => u p+c) := by
  intro p hp phi hphi ht
  have ht' : touchAbove (fun q => phi q-c) u p := by
    refine ⟨by linarith [ht.1],?_⟩
    filter_upwards [ht.2] with q hq
    change u q+c≤phi q at hq
    linarith
  have hi := hu p hp (fun q => phi q-c) (hphi.sub contDiffAt_const) ht'
  rwa [timeD_sub_const,hessian_sub_const] at hi

theorem viscositySuper_add_const {n : ℕ} {Q : Set (Point n)} {G : Sym n → Point n → ℝ}
    {g u : Point n → ℝ} (hu : viscositySuper Q G g u) (c : ℝ) :
    viscositySuper Q G g (fun p => u p+c) := by
  intro p hp phi hphi ht
  have ht' : touchBelow (fun q => phi q-c) u p := by
    refine ⟨by linarith [ht.1],?_⟩
    filter_upwards [ht.2] with q hq
    change phi q≤u q+c at hq
    linarith
  have hi := hu p hp (fun q => phi q-c) (hphi.sub contDiffAt_const) ht'
  rwa [timeD_sub_const,hessian_sub_const] at hi

theorem viscositySuper_eqOn_open {n : ℕ} {Q : Set (Point n)}
    {f v g : Point n → ℝ} {G : Sym n → Point n → ℝ}
    (hQ : IsOpen Q) (heq : Set.EqOn f v Q) (hsuper : viscositySuper Q G g v) :
    viscositySuper Q G g f := by
  intro q hq phi hphi ht
  have ht' : touchBelow phi v q := by
    refine ⟨ht.1.trans (heq hq),?_⟩
    filter_upwards [hQ.mem_nhds hq,ht.2] with y hy ht
    simpa only [heq hy] using ht
  exact hsuper q hq phi hphi ht'

end Yau.LeafProofs.L05Aux
