import Yau.LeafProofs.L05PerronMaximum
import Yau.LeafProofs.L05PerronRegularization
import Yau.LeafProofs.L05JetCombinationRules

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem perron_continuous_compare {n : ℕ} (hn : 0<n) {ell L R a b c : ℝ}
    (hell : 0<ell) (hL : ell≤L) (hR : 0<R) (hab : a<b)
    {F : Sym n → ℝ} (hF : Continuous F) (hE : globalElliptic F ell L)
    {u v : Point n → ℝ}
    (hu : ContinuousOn u (abpClosed n R a b)) (hv : ContinuousOn v (abpClosed n R a b))
    (hsub : viscositySub (abpOpen n R a b) (fun H _ => F H) (fun _ => 0) u)
    (hsuper : viscositySuper (abpOpen n R a b) (fun H _ => F H) (fun _ => 0) v)
    (hbd : ∀ p∈abpBoundary n R a b, u p≤v p+c) :
    ∀ p∈abpClosed n R a b, u p≤v p+c := by
  have hQD : abpOpen n R a b⊆abpClosed n R a b :=
    fun _ hp => ⟨Metric.ball_subset_closedBall hp.1,hp.2.1.le,hp.2.2.le⟩
  have hdiff := (parabolicJetCombination n hn ell L hell hL (abpOpen n R a b) F
    (Metric.isOpen_ball.prod isOpen_Ioo) hF hE).1 u v (hu.mono hQD) (hv.mono hQD) hsub hsuper
  let w := fun p : Point n => u p-v p-c
  have hw : ContinuousOn w (abpClosed n R a b) := by
    intro p hp
    exact ((hu p hp).sub (hv p hp)).sub continuousWithinAt_const
  have hs : viscositySub (abpOpen n R a b) (fun H _ => pucciPlus ell L H) (fun _ => 0) w := by
    convert! viscositySub_add_const hdiff (-c) using 1
  have hb : ∀ p∈abpBoundary n R a b, w p≤0 := by
    intro p hp
    dsimp only [w]
    linarith [hbd p hp]
  intro p hp
  have hh := perron_pucci_maximum hell.le hL hR hab hw hs hb p hp
  dsimp only [w] at hh
  linarith

end Yau.LeafProofs.L05Aux
