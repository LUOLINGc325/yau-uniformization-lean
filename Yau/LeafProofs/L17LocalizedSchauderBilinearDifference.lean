import Yau.LeafProofs.L17LocalizedSchauderBilinearBounds

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A true finite-order bilinear difference estimate, linear in each
factor budget, requiring only the indicated finite differentiability. -/
theorem norm_iteratedFDeriv_bilinear_sub_le (k : ℕ) (B : F →L[ℝ] G →L[ℝ] H)
    {U : Set E} (hU : IsOpen U) (f₁ f₂ : E → F) (g₁ g₂ : E → G)
    (hf₁ : ContDiffOn ℝ (k : ℕ∞ω) f₁ U) (hf₂ : ContDiffOn ℝ (k : ℕ∞ω) f₂ U)
    (hg₁ : ContDiffOn ℝ (k : ℕ∞ω) g₁ U) (hg₂ : ContDiffOn ℝ (k : ℕ∞ω) g₂ U)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) {A D ΔA ΔD : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hΔA : 0 ≤ ΔA) (hΔD : 0 ≤ ΔD)
    (hF : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f₁ x‖ ≤ A)
    (hG : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j g₂ y‖ ≤ D)
    (hFΔ : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f₁ x-iteratedFDeriv ℝ j f₂ y‖ ≤ ΔA)
    (hGΔ : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j g₁ x-iteratedFDeriv ℝ j g₂ y‖ ≤ ΔD) :
    ‖iteratedFDeriv ℝ k (fun z => B (f₁ z) (g₁ z)) x-
        iteratedFDeriv ℝ k (fun z => B (f₂ z) (g₂ z)) y‖ ≤
      ‖B‖*bilinearJetConstant k*(A*ΔD+ΔA*D) := by
  let W : Set E := (fun z => x+z) ⁻¹' U ∩ (fun z => y+z) ⁻¹' U
  have hW : IsOpen W := (hU.preimage (continuous_const.add continuous_id)).inter
    (hU.preimage (continuous_const.add continuous_id))
  have h0 : (0 : E) ∈ W := by simpa only [W,mem_inter_iff,mem_preimage,add_zero] using And.intro hx hy
  let F₁ : E → F := fun z => f₁ (x+z)
  let F₂ : E → F := fun z => f₂ (y+z)
  let G₁ : E → G := fun z => g₁ (x+z)
  let G₂ : E → G := fun z => g₂ (y+z)
  have hF₁ : ContDiffOn ℝ (k : ℕ∞ω) F₁ W :=
    hf₁.comp (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz.1)
  have hF₂ : ContDiffOn ℝ (k : ℕ∞ω) F₂ W :=
    hf₂.comp (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz.2)
  have hG₁ : ContDiffOn ℝ (k : ℕ∞ω) G₁ W :=
    hg₁.comp (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz.1)
  have hG₂ : ContDiffOn ℝ (k : ℕ∞ω) G₂ W :=
    hg₂.comp (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz.2)
  have hFBound : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j F₁ 0‖ ≤ A := by
    intro j hj
    simpa only [F₁,iteratedFDeriv_comp_add_left,add_zero] using hF j hj
  have hGBound : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j G₂ 0‖ ≤ D := by
    intro j hj
    simpa only [G₂,iteratedFDeriv_comp_add_left,add_zero] using hG j hj
  have hFDelta : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j (fun z => F₁ z-F₂ z) 0‖ ≤ ΔA := by
    intro j hj
    change ‖iteratedFDeriv ℝ j (F₁-F₂) 0‖ ≤ ΔA
    rw [iteratedFDeriv_sub_apply
      ((hF₁.contDiffAt (hW.mem_nhds h0)).of_le (by exact_mod_cast hj))
      ((hF₂.contDiffAt (hW.mem_nhds h0)).of_le (by exact_mod_cast hj))]
    simpa only [F₁,F₂,iteratedFDeriv_comp_add_left,add_zero] using hFΔ j hj
  have hGDelta : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j (fun z => G₁ z-G₂ z) 0‖ ≤ ΔD := by
    intro j hj
    change ‖iteratedFDeriv ℝ j (G₁-G₂) 0‖ ≤ ΔD
    rw [iteratedFDeriv_sub_apply
      ((hG₁.contDiffAt (hW.mem_nhds h0)).of_le (by exact_mod_cast hj))
      ((hG₂.contDiffAt (hW.mem_nhds h0)).of_le (by exact_mod_cast hj))]
    simpa only [G₁,G₂,iteratedFDeriv_comp_add_left,add_zero] using hGΔ j hj
  let q₁ : E → H := fun z => B (F₁ z) (G₁ z-G₂ z)
  let q₂ : E → H := fun z => B (F₁ z-F₂ z) (G₂ z)
  have hQ₁ : ContDiffOn ℝ (k : ℕ∞ω) q₁ W :=
    B.isBoundedBilinearMap.contDiff.comp_contDiffOn (hF₁.prodMk (hG₁.sub hG₂))
  have hQ₂ : ContDiffOn ℝ (k : ℕ∞ω) q₂ W :=
    B.isBoundedBilinearMap.contDiff.comp_contDiffOn ((hF₁.sub hF₂).prodMk hG₂)
  have hP₁ : ContDiffAt ℝ (k : ℕ∞ω) (fun z => B (F₁ z) (G₁ z)) 0 :=
    (B.isBoundedBilinearMap.contDiff.comp_contDiffOn (hF₁.prodMk hG₁)).contDiffAt (hW.mem_nhds h0)
  have hP₂ : ContDiffAt ℝ (k : ℕ∞ω) (fun z => B (F₂ z) (G₂ z)) 0 :=
    (B.isBoundedBilinearMap.contDiff.comp_contDiffOn (hF₂.prodMk hG₂)).contDiffAt (hW.mem_nhds h0)
  have hDiff : iteratedFDeriv ℝ k (fun z => B (F₁ z) (G₁ z)-B (F₂ z) (G₂ z)) 0 =
      iteratedFDeriv ℝ k (fun z => B (f₁ z) (g₁ z)) x-
        iteratedFDeriv ℝ k (fun z => B (f₂ z) (g₂ z)) y := by
    change iteratedFDeriv ℝ k ((fun z => B (F₁ z) (G₁ z))-(fun z => B (F₂ z) (G₂ z))) 0 = _
    rw [iteratedFDeriv_sub_apply hP₁ hP₂]
    change iteratedFDeriv ℝ k (fun z => (fun w => B (f₁ w) (g₁ w)) (x+z)) 0-
      iteratedFDeriv ℝ k (fun z => (fun w => B (f₂ w) (g₂ w)) (y+z)) 0 = _
    exact congrArg₂ (fun a b => a-b)
      (by simpa only [add_zero] using (iteratedFDeriv_comp_add_left (𝕜 := ℝ)
        (f := fun z : E => B (f₁ z) (g₁ z)) k x (0 : E)))
      (by simpa only [add_zero] using (iteratedFDeriv_comp_add_left (𝕜 := ℝ)
        (f := fun z : E => B (f₂ z) (g₂ z)) k y (0 : E)))
  have hDecomp : (fun z => B (F₁ z) (G₁ z)-B (F₂ z) (G₂ z)) = (fun z => q₁ z+q₂ z) := by
    funext z
    simp only [q₁,q₂,map_sub,ContinuousLinearMap.sub_apply]
    abel
  calc
    _ = ‖iteratedFDeriv ℝ k (fun z => B (F₁ z) (G₁ z)-B (F₂ z) (G₂ z)) 0‖ := congrArg norm hDiff.symm
    _ = ‖iteratedFDeriv ℝ k (fun z => q₁ z+q₂ z) 0‖ := by rw [hDecomp]
    _ ≤ ‖iteratedFDeriv ℝ k q₁ 0‖+‖iteratedFDeriv ℝ k q₂ 0‖ := by
      change ‖iteratedFDeriv ℝ k (q₁+q₂) 0‖ ≤ _
      rw [iteratedFDeriv_add_apply (hQ₁.contDiffAt (hW.mem_nhds h0)) (hQ₂.contDiffAt (hW.mem_nhds h0))]
      exact norm_add_le _ _
    _ ≤ ‖B‖*bilinearJetConstant k*A*ΔD+‖B‖*bilinearJetConstant k*ΔA*D :=
      add_le_add (norm_iteratedFDeriv_bilinear_le k B hW F₁ _ hF₁ (hG₁.sub hG₂) h0 hA hΔD hFBound hGDelta)
        (norm_iteratedFDeriv_bilinear_le k B hW _ G₂ (hF₁.sub hF₂) hG₂ h0 hΔA hD hFDelta hGBound)
    _ = _ := by ring

end Yau.LeafProofs.L17LocalizedSchauderAux
