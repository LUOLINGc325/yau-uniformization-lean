import Yau.Proofs.F05BootstrapHalfSpacePatch
import Yau.Proofs.F05BootstrapWholeSpacePatch

/-! One patch theorem treats the genuine physical halfspace and the full
space, including dimension zero. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_flat_patch_estimate (ν : Option (RIdx n)) {α M lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {K : Set (Space n)}
    (hK : IsCompact K) (hKH : K ⊆ closure (F05FlatOpen ν)) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (T : ℝ) (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
        (f u : Point n → ℝ) (X V : Set (Space n)) (φ : Space n → ℝ) (θ : ℝ → ℝ)
        (F L E0 E1 E2 H0 H1 : ℝ),
      0 < T → T ≤ δ → UniqueDiffOn ℝ X → IsOpen V →
      (closure (F05FlatOpen ν) ∩ V ⊆ X) →
      ContDiff ℝ 2 φ → tsupport φ ⊆ V → ContDiff ℝ 1 θ →
      θ =ᶠ[nhds 0] (fun _ => 0) →
      HolderBound α (cylinder (closure (F05FlatOpen ν)) 0 T) a M →
      (∀ j, HolderBound α (cylinder (closure (F05FlatOpen ν)) 0 T) (fun z => b z j) M) →
      Elliptic (cylinder (closure (F05FlatOpen ν)) 0 T) a lam upper →
      (∀ z ∈ cylinder (closure (F05FlatOpen ν)) 0 T, z.1 ∉ K → a z = 1) →
      F05RelC2 X (Icc 0 T) u →
      (∀ j, ν = some j → ∀ x ∈ X, realCoord x j = 0 → ∀ t ∈ Icc 0 T, u (x,t) = 0) →
      (∀ z ∈ X ×ˢ Icc 0 T, F05RelOp X (Icc 0 T) a b u z = f z) →
      HolderBound α ((closure (F05FlatOpen ν) ∩ V) ×ˢ Icc 0 T)
        (fun z => (u z,F05RelD X u z)) L →
      HolderBound α ((closure (F05FlatOpen ν) ∩ V) ×ˢ Icc 0 T) f F →
      HolderBound α (cylinder (closure (F05FlatOpen ν)) 0 T) (fun z => φ z.1) E0 →
      HolderBound α (cylinder (closure (F05FlatOpen ν)) 0 T) (fun z => fderiv ℝ φ z.1) E1 →
      HolderBound α (cylinder (closure (F05FlatOpen ν)) 0 T)
        (fun z => fderiv ℝ (fderiv ℝ φ) z.1) E2 →
      HolderBound α (cylinder (closure (F05FlatOpen ν)) 0 T) (fun z => θ z.2) H0 →
      HolderBound α (cylinder (closure (F05FlatOpen ν)) 0 T) (fun z => deriv θ z.2) H1 →
      F05RelSchauder α (closure (F05FlatOpen ν)) (Icc 0 T)
        (fun z => θ z.2*(φ z.1*u z))
        (C*(4*H0*E0*F+(2*H0*spatialCutoffCommutatorBudget n M E1 E2+4*H1*E0)*L)) := by
  cases ν with
  | none =>
    have hH : closure (F05FlatOpen (none : Option (RIdx n))) = univ := by
      simp only [F05FlatOpen,closure_univ]
    obtain ⟨δ,C,hδ,hδ1,hC,hEstimate⟩ :=
      F05_relative_wholeSpace_patch_estimate (M := M) (lam := lam) (upper := upper) hα hα1 hK
    refine ⟨δ,C,hδ,hδ1,hC,?_⟩
    intro T a b f u X V φ θ F L E0 E1 E2 H0 H1 hT hTδ hX hV hVX hφ hSupport hθ hZero
      ha hb hEll hExterior hu hFace hEq hLow hf hφ0 hφ1 hφ2 hθ0 hθ1
    rw [hH] at hVX ha hb hEll hExterior hLow hf hφ0 hφ1 hφ2 hθ0 hθ1 ⊢
    apply hEstimate T a b f u X V φ θ F L E0 E1 E2 H0 H1 hT hTδ hX hV
      (fun x hx => hVX ⟨mem_univ _,hx⟩) hφ hSupport hθ hZero ha hb hEll hExterior hu hEq
    · simpa only [univ_inter] using hLow
    · simpa only [univ_inter] using hf
    · exact hφ0
    · exact hφ1
    · exact hφ2
    · exact hθ0
    · exact hθ1
  | some j =>
    let e : Space n := -(realVec j)
    have he : ‖e‖ = 1 := by simp only [e,norm_neg,realVec_norm]
    have hInner (x : Space n) : inner ℝ e x = -realCoord x j := by
      rw [show e = -(realVec j) from rfl,inner_neg_left,real_inner_comm,real_inner_realVec]
    have hH : closure (F05FlatOpen (some j)) = {x : Space n | 0 ≤ inner ℝ e x} := by
      rw [F05FlatOpen_closure]
      ext x
      simp only [mem_setOf_eq,hInner,neg_nonneg]
    obtain ⟨δ,C,hδ,hδ1,hC,hEstimate⟩ :=
      F05_relative_halfSpace_patch_estimate (M := M) (lam := lam) (upper := upper)
        hα hα1 e he hK (by rwa [← hH])
    refine ⟨δ,C,hδ,hδ1,hC,?_⟩
    intro T a b f u X V φ θ F L E0 E1 E2 H0 H1 hT hTδ hX hV hVX hφ hSupport hθ hZero
      ha hb hEll hExterior hu hFace hEq hLow hf hφ0 hφ1 hφ2 hθ0 hθ1
    rw [hH] at hVX ha hb hEll hExterior hLow hf hφ0 hφ1 hφ2 hθ0 hθ1 ⊢
    apply hEstimate T a b f u X V φ θ F L E0 E1 E2 H0 H1 hT hTδ hX hV hVX
      hφ hSupport hθ hZero ha hb hEll hExterior hu ?_ hEq hLow hf hφ0 hφ1 hφ2 hθ0 hθ1
    intro x hx hx0 t ht
    exact hFace j rfl x hx (by simpa only [hInner,neg_eq_zero] using hx0) t ht

end Yau.Proofs.F05Aux
