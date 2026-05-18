
import LeanFomega.Typing
import LeanFomega.Kinding.Rename
open LeanSubst

namespace LeanFomega

structure KindingSubst (σ : Subst Ty) (Δ1 Δ2 : List Kind) where
  act : ∀ {x T}, Δ1[x]? = some T -> Δ2 ⊢ₖ σ.act x : T

notation:35 Γ:35 " -[" σ "]> " Δ:35 => KindingSubst σ Γ Δ

theorem KindingSubst.id Δ : Δ -[+0]> Δ := sorry

theorem KindingSubst.re (j : Δ2[y]? = some A) (m : Δ1 -[σ]> Δ2) : A::Δ1 -[re y::σ]> Δ2 := sorry

theorem KindingSubst.su (j : Δ2 ⊢ₖ a : A) (m : Δ1 -[σ]> Δ2) : A::Δ1 -[su a::σ]> Δ2 := sorry

theorem KindingSubst.lift A :
  Δ1 -[σ]> Δ2 ->
  A::Δ1 -[σ.lift]> A::Δ2
:= sorry

theorem KindingSubst.succ A : Δ -[+1]> A::Δ := sorry

theorem KindingSubst.comp : A -[σ]> B -> B -[τ]> C -> A -[σ ∘ τ]> C := sorry

theorem KindingRen.to (m : A -⟨r⟩> B) : A -[r.to]> B := sorry

theorem Kinding.subst (m : Δ1 -[σ]> Δ2) : Δ1 ⊢ₖ A : K -> Δ2 ⊢ₖ A[σ] : K
| var h => m.act h
| lam j => lam (j.subst $ m.lift _)
| app j1 j2 => app (j1.subst m) (j2.subst m)
| all j => all (j.subst $ m.lift _)
| arrow j1 j2 => arrow (j1.subst m) (j2.subst m)

theorem Kinding.beta : (A::Δ) ⊢ₖ b : B -> Δ ⊢ₖ t : A -> Δ ⊢ₖ b[su t::+0] : B
| j1, j2 => subst (.su j2 $ .id _) j1

end LeanFomega
