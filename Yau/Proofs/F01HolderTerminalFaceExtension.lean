import Yau.Proofs.F01HolderComposition
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! A genuine Holder field and its constructed terminal slice extend
with the same bound to the closed terminal face. The proof passes the
original estimates to actual pointwise limits. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]

def closeTerminalTimeFace (f : Point n → F) (b : Space n → F) (T : ℝ) (p : Point n) : F :=
  if p.2 = T then b p.1 else f p

theorem holderBound_close_terminal_time_face
    (S : Set (Space n)) (f : Point n → F) (b : Space n → F)
    {l T β C : ℝ} (hβ : 0 ≤ β)
    (hf : HolderBound β (S ×ˢ Ioo l T) f C)
    (τ : ℕ → ℝ) (hτ : ∀ m, τ m ∈ Ioo l T) (hLim : Tendsto τ atTop (𝓝 T))
    (hValues : ∀ x ∈ S, Tendsto (fun m => f (x, τ m)) atTop (𝓝 (b x))) :
    HolderBound β (S ×ˢ Ioc l T) (closeTerminalTimeFace f b T) C := by
  classical
  let w : Point n → ℕ → Point n := fun p m => (p.1, if p.2 = T then τ m else p.2)
  have hInto (p : Point n) (hp : p ∈ S ×ˢ Ioc l T) (m : ℕ) : w p m ∈ S ×ˢ Ioo l T := by
    change p.1 ∈ S ∧ (if p.2 = T then τ m else p.2) ∈ Ioo l T
    by_cases he : p.2 = T
    · rw [if_pos he]
      exact ⟨hp.1, hτ m⟩
    · have hlt : p.2 < T := by
        rcases lt_or_eq_of_le hp.2.2 with hh | hh
        · exact hh
        · exact (he hh).elim
      rw [if_neg he]
      exact ⟨hp.1, hp.2.1, hlt⟩
  have hPoint (p : Point n) : Tendsto (w p) atTop (𝓝 p) := by
    by_cases he : p.2 = T
    · have hh : Tendsto (fun m => (p.1, τ m)) atTop (𝓝 (p.1, T)) :=
        tendsto_const_nhds.prodMk_nhds hLim
      change Tendsto (fun m => (p.1, if p.2 = T then τ m else p.2)) atTop (𝓝 p)
      simp only [if_pos he]
      have hPair : (p.1, T) = p := Prod.ext rfl he.symm
      rw [hPair] at hh
      exact hh
    · change Tendsto (fun m => (p.1, if p.2 = T then τ m else p.2)) atTop (𝓝 p)
      simp only [if_neg he]
      exact tendsto_const_nhds
  have hField (p : Point n) (hp : p ∈ S ×ˢ Ioc l T) :
      Tendsto (fun m => f (w p m)) atTop (𝓝 (closeTerminalTimeFace f b T p)) := by
    by_cases he : p.2 = T
    · change Tendsto (fun m => f (p.1, if p.2 = T then τ m else p.2)) atTop
        (𝓝 (if p.2 = T then b p.1 else f p))
      simp only [if_pos he]
      exact hValues p.1 hp.1
    · change Tendsto (fun m => f (p.1, if p.2 = T then τ m else p.2)) atTop
        (𝓝 (if p.2 = T then b p.1 else f p))
      simp only [if_neg he]
      exact tendsto_const_nhds
  refine ⟨hf.1, ?_, ?_⟩
  · intro p hp
    exact le_of_tendsto (hField p hp).norm
      (Eventually.of_forall (fun m => hf.2.1 _ (hInto p hp m)))
  · intro p hp q hq
    have hNorm : Tendsto (fun m => ‖f (w p m) - f (w q m)‖) atTop
        (𝓝 ‖closeTerminalTimeFace f b T p - closeTerminalTimeFace f b T q‖) :=
      ((hField p hp).sub (hField q hq)).norm
    have hTime : Tendsto (fun m => |(w p m).2 - (w q m).2|) atTop (𝓝 |p.2 - q.2|) :=
      ((hPoint p).snd_nhds.sub ((hPoint q).snd_nhds)).abs
    have hWeightLim : Tendsto (fun m => holderWeight β (w p m) (w q m)) atTop
        (𝓝 (holderWeight β p q)) := by
      change Tendsto (fun m => ‖p.1 - q.1‖ ^ β + |(w p m).2 - (w q m).2| ^ (β / 2)) atTop
        (𝓝 (‖p.1 - q.1‖ ^ β + |p.2 - q.2| ^ (β / 2)))
      exact tendsto_const_nhds.add (hTime.rpow_const (Or.inr (by positivity : 0 ≤ β / 2)))
    have hW : Tendsto (fun m => C * holderWeight β (w p m) (w q m)) atTop
        (𝓝 (C * holderWeight β p q)) := hWeightLim.const_mul C
    exact le_of_tendsto_of_tendsto hNorm hW
      (Eventually.of_forall (fun m => hf.2.2 _ (hInto p hp m) _ (hInto q hq m)))

end Yau.NodeProofs.F01Aux
