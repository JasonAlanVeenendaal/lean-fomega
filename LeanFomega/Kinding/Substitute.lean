
import LeanFomega.Typing
import LeanFomega.Kinding.Rename
open LeanSubst

namespace LeanFomega

structure KindingSubst (σ : Subst Ty) (Δ1 Δ2 : List Kind) where
  act : ∀ {x T}, Δ1[x]? = some T -> Δ2 ⊢ₖ σ.act x : T

notation:35 Γ:35 " -[" σ "]> " Δ:35 => KindingSubst σ Γ Δ

theorem KindingSubst.re (j : Δ2[y]? = some A) (m : Δ1 -[σ]> Δ2) : A::Δ1 -[re y::σ]> Δ2 := sorry

theorem KindingSubst.su (j : Δ2 ⊢ₖ a : A) (m : Δ1 -[σ]> Δ2) : A::Δ1 -[su a::σ]> Δ2 := sorry

theorem Kinding.comp : A -[σ]> B -> B -[τ]> C -> A -[σ ∘ τ]> C := sorry

theorem Kinding.subst (m : Δ1 -[σ]> Δ2) : Δ1 ⊢ₖ A : K -> Δ2 ⊢ₖ A[σ] : K := sorry

theorem Kinding.beta : (A::Δ) ⊢ₖ b : B -> Δ ⊢ₖ t : A -> Δ ⊢ₖ b[su t::+0] : B := sorry

end LeanFomega
